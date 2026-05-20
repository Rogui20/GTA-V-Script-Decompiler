using Decompiler.Ast;
using Decompiler.Ast.StatementTree;
using System;
using System.Collections.Generic;
using System.Reflection;
using System.Text;
using System.Text.RegularExpressions;

namespace Decompiler.Emitters
{
    /// <summary>
    /// Minimal Lua backend prototype.
    /// This is intentionally conservative and only supports a limited subset to prove backend pluggability.
    /// Future expansions should map additional AstToken/Tree types here without touching decode logic.
    /// </summary>
    internal class LuaEmitter : IEmitter
    {
        private int switchTempIndex = 0;
        private readonly HashSet<string> vectorLocals = new();

        private enum MemoryKind { Local, Global, Ref, StructLocal, Unknown }
        private record MemoryAddress(MemoryKind Kind, string BaseName, string BaseIndex, string OffsetExpr, bool IsAddressable);

        public string EmitFunction(Function func)
        {
            StringBuilder sb = new();
            sb.AppendLine($"function {func.Name}({GetFunctionParamList(func)})") ;
            EmitFunctionLocals(sb, func, 1);
            EmitTreeBody(sb, func.MainTree, 1, false);
            sb.AppendLine("end");
            return sb.ToString();
        }

        public string EmitScript(ScriptFile file)
        {
            StringBuilder sb = new();
            sb.AppendLine("Local = Local or {}");
            sb.AppendLine("Global = Global or {}");
            sb.AppendLine();
            EmitRuntimeHelpers(sb);

            // Script-level locals are emitted at the top so Lua output keeps variable context
            // similar to the current C-like output and can be expanded later for richer mappings.
            if (file.Header.StaticsCount > 0)
            {
                foreach (var declaration in file.Statics.GetDeclaration())
                {
                    sb.AppendLine(ConvertStaticDeclaration(declaration));
                }

                sb.AppendLine();
            }

            foreach (var func in file.Functions)
            {
                sb.AppendLine(EmitFunction(func));
            }

            var result = sb.ToString();
            var warns = BuildWarnings(result);
            if (warns.Length > 0)
            {
                StringBuilder wb = new();
                wb.AppendLine("-- LUA_EMITTER_FATAL_PATTERNS_FOUND");
                foreach (var w in warns) wb.AppendLine($"-- found invalid token: {w}");
                wb.AppendLine();
                wb.Append(result);
                result = wb.ToString();
            }
            return result;
        }

        private void EmitTreeBody(StringBuilder sb, Tree tree, int indent, bool insideSwitchCase)
        {
            foreach (var statement in tree.Statements)
            {
                EmitNode(sb, statement, indent, insideSwitchCase);
            }
        }

        private void EmitNode(StringBuilder sb, object node, int indent, bool insideSwitchCase)
        {
            switch (node)
            {
                case If i:
                    EmitIf(sb, i, indent);
                    break;
                case While w:
                    EmitWhile(sb, w, indent);
                    break;
                case Switch sw:
                    EmitSwitch(sb, sw, indent);
                    break;
                case For f:
                    EmitFor(sb, f, indent);
                    break;
                case AstToken token:
                    EmitTokenStatement(sb, token, indent, insideSwitchCase);
                    break;
                case Tree nested:
                    EmitTreeBody(sb, nested, indent, insideSwitchCase);
                    break;
                default:
                    AppendLine(sb, indent, $"-- TODO unsupported token: {node.GetType().FullName}");
                    break;
            }
        }

        private void EmitIf(StringBuilder sb, If node, int indent)
        {
            AppendLine(sb, indent, $"if {ConvertExpression(node.Condition)} then");
            EmitTreeBody(sb, node, indent + 1, false);

            foreach (var elseIf in node.ElseIfTrees)
            {
                AppendLine(sb, indent, $"elseif {ConvertExpression(elseIf.Condition)} then");
                EmitTreeBody(sb, elseIf, indent + 1, false);
            }

            if (node.ElseTree != null)
            {
                AppendLine(sb, indent, "else");
                EmitTreeBody(sb, node.ElseTree, indent + 1, false);
            }

            AppendLine(sb, indent, "end");
        }

        private void EmitWhile(StringBuilder sb, While node, int indent)
        {
            AppendLine(sb, indent, $"while {ConvertExpression(node.Condition)} do");
            EmitTreeBody(sb, node, indent + 1, false);
            AppendLine(sb, indent, "end");
        }

        private void EmitSwitch(StringBuilder sb, Switch node, int indent)
        {
            string tempVar = $"__switch_{switchTempIndex++}";
            AppendLine(sb, indent, $"local {tempVar} = {ConvertExpression(node.SwitchVal)}");

            bool first = true;
            Case? defaultCase = null;
            foreach (var stmt in node.Statements)
            {
                if (stmt is not Case c)
                    continue;

                int caseCodeOffset = node.Function.FunctionOffsetToCodeOffset(c.StartOffset);
                if (!node.Cases.TryGetValue(caseCodeOffset, out var caseLabels) || caseLabels.Count == 0)
                    continue;
                bool isDefault = caseLabels[0] is Default;

                if (isDefault)
                {
                    defaultCase = c;
                    continue;
                }

                // First label in case block drives the if/elseif guard.
                AstToken firstLabel = caseLabels[0];
                string guard = $"{tempVar} == {ConvertExpression(firstLabel)}";
                AppendLine(sb, indent, first ? $"if {guard} then" : $"elseif {guard} then");
                EmitTreeBody(sb, c, indent + 1, true);
                first = false;
            }

            if (defaultCase != null)
            {
                if (defaultCase.Statements.Count > 0)
                {
                    AppendLine(sb, indent, first ? "if true then" : "else");
                    EmitTreeBody(sb, defaultCase, indent + 1, true);
                }
            }

            if (!first || defaultCase != null)
                AppendLine(sb, indent, "end");
        }

        private void EmitFor(StringBuilder sb, For node, int indent)
        {
            if (TryEmitNumericFor(sb, node, indent))
                return;

            // Fallback safe lowering if we cannot infer Lua numeric-for shape.
            AppendLine(sb, indent, "do");
            AppendLine(sb, indent + 1, ConvertStatement(node.Initializer.ToString()));
            AppendLine(sb, indent + 1, $"while {ConvertExpression(node.Condition)} do");
            EmitTreeBody(sb, node, indent + 2, false);
            AppendLine(sb, indent + 2, ConvertStatement(node.Increment.ToString()));
            AppendLine(sb, indent + 1, "end");
            AppendLine(sb, indent, "end");
        }

        private bool TryEmitNumericFor(StringBuilder sb, For node, int indent)
        {
            string init = ConvertStatement(node.Initializer.ToString());
            var mInit = Regex.Match(init, @"^([A-Za-z_]\w*)\s*=\s*(.+)$");
            if (!mInit.Success)
                return false;

            string varName = mInit.Groups[1].Value;
            string startExpr = mInit.Groups[2].Value;
            string cond = ConvertExpression(node.Condition);
            string incr = ConvertStatement(node.Increment.ToString());

            string pattern = @"^" + Regex.Escape(varName) + @"\s*(<|<=)\s*(.+)$";
            var mCond = Regex.Match(cond, pattern);
            if (!mCond.Success)
                return false;

            var mIncr = Regex.Match(incr, @"^" + Regex.Escape(varName) + @"\s*=\s*" + Regex.Escape(varName) + @"\s*\+\s*1(\.0)?$");
            if (!mIncr.Success)
                return false;

            string op = mCond.Groups[1].Value.Trim();
            string endExclusive = mCond.Groups[2].Value.Trim();
            string endExpr = op == "<=" ? endExclusive : $"{endExclusive} - 1";
            AppendLine(sb, indent, $"for {varName} = {startExpr}, {endExpr} do");
            EmitTreeBody(sb, node, indent + 1, false);
            AppendLine(sb, indent, "end");
            return true;
        }

        private void EmitTokenStatement(StringBuilder sb, AstToken token, int indent, bool insideSwitchCase)
        {
            switch (token)
            {
                case Return ret:
                    EmitReturn(sb, ret, indent);
                    break;
                case LocalStore or StaticStore or GlobalStore or ArrayStore or OffsetStore or Store:
                    AppendLine(sb, indent, ConvertStatement(token.ToString()));
                    break;
                case StoreN storeN:
                    AppendLine(sb, indent, ConvertStoreN(storeN));
                    break;
                case NativeCall nativeCall when nativeCall.IsStatement():
                    AppendLine(sb, indent, ConvertNativeStatement(nativeCall));
                    break;
                case Drop drop:
                    AppendLine(sb, indent, ConvertDrop(drop));
                    break;
                case Break:
                    if (!insideSwitchCase)
                        AppendLine(sb, indent, "break");
                    break;
                case FunctionCallBase call when call.IsStatement():
                    AppendLine(sb, indent, ConvertStatement(call.ToString()));
                    break;
                default:
                    AppendLine(sb, indent, $"-- TODO unsupported token: {token.GetType().FullName}");
                    break;
            }
        }

        private void EmitReturn(StringBuilder sb, Return ret, int indent)
        {
            if (ret.ReturnValues.Count == 0)
            {
                AppendLine(sb, indent, "return");
                return;
            }

            if (ret.ReturnValues.Count == 1 && ret.function.NumReturns > 1)
            {
                string baseExpr = ConvertExpression(ret.ReturnValues[0]);
                var memMatch = Regex.Match(baseExpr, @"^(Local|Global)\[(.+)\]$");
                if (memMatch.Success)
                {
                    string mem = memMatch.Groups[1].Value;
                    string idx = memMatch.Groups[2].Value;
                    List<string> vals = new();
                    for (int i = 0; i < ret.function.NumReturns; i++)
                    {
                        vals.Add(i == 0 ? $"{mem}[{idx}]" : $"{mem}[{idx} + {i}]");
                    }

                    AppendLine(sb, indent, $"return {string.Join(", ", vals)}");
                    return;
                }
            }

            StringBuilder values = new();
            var first = true;
            foreach (var v in ret.ReturnValues)
            {
                if (!first)
                    values.Append(", ");
                values.Append(ConvertExpression(v));
                first = false;
            }

            AppendLine(sb, indent, $"return {values}");
        }

        private static string ConvertNativeStatement(NativeCall call)
        {
            string c = call.ToString();
            int paren = c.IndexOf('(');
            string argsPart = paren >= 0 ? c.Substring(paren) : "()";
            string name = call.Name.Replace("::", ".").ToUpperInvariant();
            return ConvertStatement($"{name}{argsPart}");
        }

        private static string ConvertExpression(AstToken token)
        {
            string value = token is NativeCall native
                ? ConvertNativeExpression(native)
                : token.ToString();
            return NormalizeResolvedArtifacts(ConvertMemoryModel(ConvertOperators(ConvertFloatLiterals(ConvertNamespaces(value.TrimEnd(';'))))));
        }

        private static string ConvertNativeExpression(NativeCall call)
        {
            string c = call.ToString();
            int paren = c.IndexOf('(');
            string argsPart = paren >= 0 ? c.Substring(paren) : "()";
            string name = call.Name.Replace("::", ".").ToUpperInvariant();
            return $"{name}{argsPart}";
        }

        private static string ConvertStatement(string statement)
        {
            return NormalizeResolvedArtifacts(ConvertMemoryModel(ConvertOperators(ConvertFloatLiterals(ConvertNamespaces(statement.TrimEnd(';'))))));
        }

        private static string ConvertStaticDeclaration(string declaration)
        {
            string line = declaration.Trim().TrimEnd(';');
            int eq = line.IndexOf(" = ", StringComparison.Ordinal);
            if (eq < 0)
                return $"-- TODO unsupported token: static declaration {line}";

            string left = line.Substring(0, eq).Trim();
            string right = line[(eq + 3)..].Trim();

            int lastSpace = left.LastIndexOf(' ');
            string varName = lastSpace >= 0 ? left[(lastSpace + 1)..] : left;

            string value = ConvertStatement(right);
            if (left.StartsWith("char*", StringComparison.OrdinalIgnoreCase) && value == "0")
                value = "nil";
            else if ((left.StartsWith("BOOL", StringComparison.OrdinalIgnoreCase) || left.StartsWith("bool", StringComparison.OrdinalIgnoreCase)) && value is "0" or "1")
                value = value == "1" ? "true" : "false";

            var lm = Regex.Match(varName, @"^[a-zA-Z]+Local_(\d+)$");
            if (lm.Success)
                return $"Local[{lm.Groups[1].Value}] = {value}";
            var gm = Regex.Match(varName, @"^Global_(\d+)$");
            if (gm.Success)
                return $"Global[{gm.Groups[1].Value}] = {value}";

            return $"local {varName} = {value}";
        }

        private static string ConvertOperators(string input)
        {
            string output = input.Replace("&&", "and").Replace("||", "or");
            output = output.Replace("!=", "~=");
            output = output.Replace("!", "not ");
            output = Regex.Replace(output, @"\b([A-Za-z_]\w*|\d+)\s*&\s*([A-Za-z_]\w*|\d+)\b", "BitAnd($1, $2)");
            return output;
        }

        private static string ConvertFloatLiterals(string input)
        {
            string output = Regex.Replace(input, @"(?<![\w.])(-?\d+\.\d+)f\b", "$1");
            output = Regex.Replace(output, @"(?<![\w.])(-?\d+)f\b", "$1.0");
            return output;
        }

        private static string ConvertNamespaces(string input)
        {
            return input.Replace("::", ".");
        }

        private static string ConvertMemoryModel(string input)
        {
            string output = input;
            output = ReplacePointerAssignments(output);
            output = ReplacePointerReads(output);
            output = Regex.Replace(output, @"&\s*Local\[(.+?)\]", "LocalRef($1)");
            output = Regex.Replace(output, @"&\s*Global\[(.+?)\]", "GlobalRef($1)");
            output = Regex.Replace(output, @"&\(([^)]+)\)", m => ConvertRefExpression(m.Groups[1].Value));
            output = ReplaceMemoryRefs(output, true);
            output = ReplaceMemoryRefs(output, false);
            // Final pass: after memory lowering we may still have &Local[...] / &Global[...] in nested call arguments.
            output = Regex.Replace(output, @"&\s*Local\[(.+?)\]", "LocalRef($1)");
            output = Regex.Replace(output, @"&\s*Global\[(.+?)\]", "GlobalRef($1)");
            output = Regex.Replace(output, @"&\s*([A-Za-z_]\w*)", "VarRef(function() return $1 end, function(v) $1 = v end)");
            output = Regex.Replace(output, @"\b(vParam\w*|outPosition|unk\d+)\.f_0\b", "$1.x");
            output = Regex.Replace(output, @"\b(vParam\w*|outPosition|unk\d+)\.f_1\b", "$1.y");
            output = Regex.Replace(output, @"\b(vParam\w*|outPosition|unk\d+)\.f_2\b", "$1.z");
            output = Regex.Replace(output, @"BUILTIN\.VMAG\(([^)]+)\)", "BUILTIN.VMAG(VecUnpack($1))");
            output = Regex.Replace(output, @"BUILTIN\.VDIST2?\(([^,]+),\s*([^)]+)\)", "BUILTIN.VDIST($1, $2)");
            output = output.Replace("/*", "--").Replace("*/", "");
            output = output.Replace("(float)", "");
            output = Regex.Replace(output, @"RefGet\(([^)]+)\)\s*=\s*(.+)$", "RefSet($1, $2)");
            return output;
        }

        private static string ReplacePointerAssignments(string input)
        {
            string output = input;


            // uParam1->[i /*5*/].f_1 = v
            output = Regex.Replace(output, @"\b([A-Za-z_]\w*)->\[(.*?)\]\.f_(\d+)\s*(?<![=!<>])=(?!=)\s*(.+)$", m =>
            {
                string ptr=m.Groups[1].Value; string idx=ConvertInlineArrayIndex(m.Groups[2].Value.Trim()); string f=m.Groups[3].Value; string v=m.Groups[4].Value;
                return $"RefSet({ptr}, {v}, ({idx}) + {f})";
            });
            // uParam1->f_221[i /*5*/].f_1 = v
            output = Regex.Replace(output, @"\b([A-Za-z_]\w*)->((?:f_\d+\.)*)\[(.*?)\]\.f_(\d+)\s*(?<![=!<>])=(?!=)\s*(.+)$", m =>
            {
                string ptr=m.Groups[1].Value; string pre=m.Groups[2].Value; string idx=ConvertInlineArrayIndex(m.Groups[3].Value.Trim()); string f=m.Groups[4].Value; string v=m.Groups[5].Value;
                string preOff = BuildOffsetExpr(pre + "f_0", "").Replace(" + 0", "").Trim();
                string off = (preOff == "0" || preOff == "") ? idx : $"{preOff} + ({idx})";
                return $"RefSet({ptr}, {v}, {off} + {f})";
            });
            // uParam0->f_1.f_2[expr /*stride*/] = value  => RefSet(uParam0, value, offsetExpr)
            output = Regex.Replace(output, @"\b([A-Za-z_]\w*)->((?:f_\d+\.)*f_\d+)(\[[^\]]+\])?\s*(?<![=!<>])=(?!=)\s*(.+)$", m =>
            {
                string ptr = m.Groups[1].Value;
                string fields = m.Groups[2].Value;
                string arr = m.Groups[3].Value;
                string value = m.Groups[4].Value;
                string offset = BuildOffsetExpr(fields, arr);
                return $"RefSet({ptr}, {value}, {offset})";
            });

            // *uParam0 = value  => RefSet(uParam0, value)
            output = Regex.Replace(output, @"^\*([A-Za-z_]\w*)\s*(?<![=!<>])=(?!=)\s*(.+)$", "RefSet($1, $2)");
            return output;
        }

        private static string ReplacePointerReads(string input)
        {
            string output = input;
            // uParam0->[i /*4*/].f_3 => RefGet(uParam0, (i * 4) + 3)
            output = Regex.Replace(output, @"\b([A-Za-z_]\w*)->\[(.*?)\]\.f_(\d+)", m =>
            {
                string ptr = m.Groups[1].Value;
                string idx = m.Groups[2].Value.Trim();
                string field = m.Groups[3].Value;
                string idxExpr = ConvertInlineArrayIndex(idx);
                return $"RefGet({ptr}, ({idxExpr}) + {field})";
            });
            // uParam0->[i /*4*/] => RefGet(uParam0, i * 4)
            output = Regex.Replace(output, @"\b([A-Za-z_]\w*)->\[(.*?)\]", m =>
            {
                string ptr = m.Groups[1].Value;
                string idx = m.Groups[2].Value.Trim();
                return $"RefGet({ptr}, {ConvertInlineArrayIndex(idx)})";
            });
            // uParam0->f_1.f_2[expr] => RefGet(uParam0, offsetExpr)
            output = Regex.Replace(output, @"\b([A-Za-z_]\w*)->((?:f_\d+\.)*f_\d+)(\[[^\]]+\])?", m =>
            {
                string ptr = m.Groups[1].Value;
                string fields = m.Groups[2].Value;
                string arr = m.Groups[3].Value;
                string offset = BuildOffsetExpr(fields, arr);
                return $"RefGet({ptr}, {offset})";
            });

            // *uParam0 => RefGet(uParam0)
            output = Regex.Replace(output, @"\*([A-Za-z_]\w+)", "RefGet($1)");
            return output;
        }

        private static string BuildOffsetExpr(string fields, string arr)
        {
            int sum = 0;
            foreach (Match fm in Regex.Matches(fields, @"f_(\d+)"))
                sum += int.Parse(fm.Groups[1].Value);
            string expr = sum.ToString();
            if (!string.IsNullOrEmpty(arr))
            {
                var am = Regex.Match(arr, @"\[(.*?)\]");
                if (am.Success)
                {
                    string inside = am.Groups[1].Value.Trim();
                    var sm = Regex.Match(inside, @"^(.*?)\s*/\*\s*(\d+)\s*\*/\s*$");
                    if (sm.Success)
                    {
                        string idx = sm.Groups[1].Value.Trim();
                        string stride = sm.Groups[2].Value.Trim();
                        expr += $" + ({idx} * {stride})";
                    }
                    else
                    {
                        expr += $" + {inside}";
                    }
                }
            }
            return expr;
        }

        private static string ConvertInlineArrayIndex(string inside)
        {
            var sm = Regex.Match(inside, @"^(.*?)\s*/\*\s*(\d+)\s*\*/\s*$");
            if (sm.Success)
            {
                string idx = sm.Groups[1].Value.Trim();
                string stride = sm.Groups[2].Value.Trim();
                return $"{idx} * {stride}";
            }
            return inside;
        }

        private static string ConvertRefExpression(string inner)
        {
            string mem = inner.Trim();
            var ptrAny = Regex.Match(mem, @"^([A-Za-z_]\w*)->((?:f_\d+\.)*f_\d+)?(\[[^\]]+\])?(?:\.f_(\d+))?$");
            if (ptrAny.Success)
            {
                string ptr = ptrAny.Groups[1].Value;
                string fields = ptrAny.Groups[2].Success && ptrAny.Groups[2].Value.Length>0 ? ptrAny.Groups[2].Value : "f_0";
                string arr = ptrAny.Groups[3].Success ? ptrAny.Groups[3].Value : "";
                string off = BuildOffsetExpr(fields, arr).Replace(" + 0", "").Trim();
                if (ptrAny.Groups[4].Success) off += $" + {ptrAny.Groups[4].Value}";
                if (off == "0" || off == "") off = "0";
                return $"RefAt({ptr}, {off})";
            }
            mem = ReplaceMemoryRefs(mem, true);
            mem = ReplaceMemoryRefs(mem, false);
            var ml = Regex.Match(mem, @"^Local\[(.+)\]$");
            if (ml.Success)
                return $"LocalRef({ml.Groups[1].Value})";
            var mg = Regex.Match(mem, @"^Global\[(.+)\]$");
            if (mg.Success)
                return $"GlobalRef({mg.Groups[1].Value})";
            return mem;
        }

        private static string ReplaceMemoryRefs(string input, bool local)
        {
            string prefix = local ? "Local" : "Global";
            string pat = local
                ? @"\b[a-zA-Z]+Local_(\d+)(\[[^\]]+\])?((?:\.f_\d+)*)(\[[^\]]+\])?"
                : @"\bGlobal_(\d+)(\[[^\]]+\])?((?:\.f_\d+)*)(\[[^\]]+\])?";
            return Regex.Replace(input, pat, m =>
            {
                int baseIdx = int.Parse(m.Groups[1].Value);
                int sum = baseIdx;
                foreach (Match fm in Regex.Matches(m.Groups[3].Value, @"\.f_(\d+)"))
                    sum += int.Parse(fm.Groups[1].Value);

                string expr = sum.ToString();
                string arr1 = m.Groups[2].Value;
                string arr2 = m.Groups[4].Value;
                if (!string.IsNullOrEmpty(arr1))
                {
                    expr += ConvertArrayIndexToOffset(arr1);
                }
                if (!string.IsNullOrEmpty(arr2))
                {
                    expr += ConvertArrayIndexToOffset(arr2);
                }
                return $"{prefix}[{expr}]";
            });
        }

        private static string ConvertArrayIndexToOffset(string arrToken)
        {
            var am = Regex.Match(arrToken, @"\[(.*?)\]");
            if (!am.Success)
                return "";
            string inside = am.Groups[1].Value.Trim();
            var sm = Regex.Match(inside, @"^(.*?)\s*/\*\s*(\d+)\s*\*/\s*$");
            if (sm.Success)
            {
                string idx = sm.Groups[1].Value.Trim();
                string stride = sm.Groups[2].Value.Trim();
                return $" + ({idx} * {stride})";
            }
            return $" + {inside}";
        }

        private void EmitFunctionLocals(StringBuilder sb, Function func, int indent)
        {
            vectorLocals.Clear();
            foreach (var decl in func.Vars.GetDeclaration())
            {
                string line = decl.Trim().TrimEnd(';');
                int sp = line.LastIndexOf(' ');
                if (sp < 0)
                    continue;
                string name = line[(sp + 1)..];
                if (Regex.IsMatch(name, @"^[a-zA-Z]+Local_\d+$"))
                    continue;
                AppendLine(sb, indent, $"local {name}");
            }
            if (func.Vars.GetDeclaration().Count > 0)
                sb.AppendLine();
        }

        private static string GetFunctionParamList(Function func)
        {
            List<string> names = new();
            for (int i = 0; i < func.Params.Vars.Count; i++)
            {
                var param = func.Params.Vars[i];
                if (!param.Is_Used)
                    continue;
                string name = string.IsNullOrEmpty(param.Name) ? func.Params.GetVarName((uint)i) : param.Name;
                names.Add(name);
            }

            return string.Join(", ", names);
        }

        private string ConvertStoreN(StoreN storeN)
        {
            object? ptr = GetPrivateField(storeN, "Pointer");
            object? cnt = GetPrivateField(storeN, "Count");
            object? valsObj = GetPrivateField(storeN, "Values");
            var values = valsObj as List<AstToken>;

            string? baseExpr = TryGetMemoryBaseIndex(ptr);
            string valueExpr = values != null && values.Count > 0
                ? string.Join(", ", values.ConvertAll(ConvertExpression))
                : ConvertStatement(storeN.ToString());
            string? countExpr = cnt != null ? ConvertExpressionFromObject(cnt) : null;

            // Fallback for static-pointer StoreN where pointer token does not stringify as Local[...] directly.
            // Example debug case:
            //   input text: iLocal_962 = { func_112() };
            //   output:     StoreN(Local, 962, 2, func_112())
            if (baseExpr == null && ptr?.GetType().Name == "Static")
            {
                var text = storeN.ToString();
                var m = Regex.Match(text, @"\b[a-zA-Z]+Local_(\d+)\s*=\s*\{\s*(.+?)\s*\};$");
                if (m.Success)
                {
                    baseExpr = m.Groups[1].Value;
                    valueExpr = ConvertStatement(m.Groups[2].Value);
                }
            }
            // Fallback for array-pointer StoreN, e.g.:
            // iLocal_962.f_585[0 /*3*/] = { func_51(...) };
            if (baseExpr == null && ptr?.GetType().Name == "Array")
            {
                var text = storeN.ToString();
                var m = Regex.Match(text, @"\b([a-zA-Z]+Local_(\d+)|Global_(\d+))((?:\.f_\d+)*)(\[[^\]]+\])\s*=\s*\{\s*(.+?)\s*\};$");
                if (m.Success)
                {
                    bool isGlobal = m.Groups[3].Success;
                    int baseIdx = int.Parse(isGlobal ? m.Groups[3].Value : m.Groups[2].Value);
                    int fieldSum = 0;
                    foreach (Match fm in Regex.Matches(m.Groups[4].Value, @"\.f_(\d+)"))
                        fieldSum += int.Parse(fm.Groups[1].Value);
                    baseExpr = $"{baseIdx + fieldSum}{ConvertArrayIndexToOffset(m.Groups[5].Value)}";
                    valueExpr = ConvertStoreNValue(m.Groups[6].Value, countExpr);
                    if (isGlobal && !string.IsNullOrWhiteSpace(countExpr))
                        return $"StoreN(Global, {baseExpr}, {countExpr}, {valueExpr})";
                }
            }
            if (baseExpr == null && ptr?.GetType().Name == "Offset")
            {
                var text = storeN.ToString();
                var mRef = Regex.Match(text, @"^([A-Za-z_]\w+)->((?:f_\d+\.)*f_\d+)\s*=\s*\{\s*(.+?)\s*\};$");
                if (mRef.Success && !string.IsNullOrWhiteSpace(countExpr))
                {
                    string off = BuildOffsetExpr(mRef.Groups[2].Value, "");
                    string val = ConvertStoreNValue(mRef.Groups[3].Value, countExpr);
                    return $"StoreNRef({mRef.Groups[1].Value}, {off}, {countExpr}, {val})";
                }
                var mG = Regex.Match(text, @"^Global_(\d+)((?:\.f_\d+)*)\s*=\s*\{\s*(.+?)\s*\};$");
                if (mG.Success && !string.IsNullOrWhiteSpace(countExpr))
                {
                    int baseIdx = int.Parse(mG.Groups[1].Value);
                    int fieldSum = 0;
                    foreach (Match fm in Regex.Matches(mG.Groups[2].Value, @"\.f_(\d+)")) fieldSum += int.Parse(fm.Groups[1].Value);
                    return $"StoreN(Global, {baseIdx + fieldSum}, {countExpr}, {ConvertStoreNValue(mG.Groups[3].Value, countExpr)})";
                }
            }
            if (baseExpr == null && ptr?.GetType().Name == "LocalLoad")
            {
                var text = storeN.ToString();
                var m = Regex.Match(text, @"^\*([A-Za-z_]\w+)\s*=\s*\{\s*(.+?)\s*\};$");
                if (m.Success && !string.IsNullOrWhiteSpace(countExpr))
                    return $"StoreNRef({m.Groups[1].Value}, 0, {countExpr}, {ConvertStoreNValue(m.Groups[2].Value, countExpr)})";
            }
            if (baseExpr == null && ptr?.GetType().Name == "Local")
            {
                var text = storeN.ToString();
                var m = Regex.Match(text, @"^([A-Za-z_]\w+)\s*=\s*\{\s*(.+?)\s*\};$");
                if (m.Success && countExpr == "3")
                {
                    vectorLocals.Add(m.Groups[1].Value);
                    return $"{m.Groups[1].Value} = Vec3({ConvertStoreNValue(m.Groups[2].Value, countExpr)})";
                }
            }

            if (baseExpr == null)
                return $"-- TODO StoreN unsupported: ptr={ptr?.GetType().Name}, count={countExpr}, text={SanitizeTodoText(storeN.ToString())}";

            if (!string.IsNullOrWhiteSpace(countExpr))
                return $"StoreN(Local, {baseExpr}, {countExpr}, {valueExpr})";
            return $"-- TODO StoreN unsupported: ptr={ptr?.GetType().Name}, count=<null>, text={SanitizeTodoText(storeN.ToString())}";
        }

        private string ConvertStoreNValue(string expr, string? countExpr)
        {
            var c = (countExpr ?? "").Trim();
            var converted = ConvertStatement(expr);
            if (c == "3")
            {
                var mr = Regex.Match(converted, @"^RefGet\((.+)\)$");
                if (mr.Success)
                    return $"RefN({mr.Groups[1].Value}, 0, 3)";
                if (Regex.IsMatch(converted, @"^(Local|Global)\[.+\]$"))
                    var mm = Regex.Match(converted, @"^(Local|Global)\[(.+)\]$");
                    if (mm.Success)
                        return $"{mm.Groups[1].Value}[{mm.Groups[2].Value}], {mm.Groups[1].Value}[{mm.Groups[2].Value} + 1], {mm.Groups[1].Value}[{mm.Groups[2].Value} + 2]";
                    return $"{converted}, {converted}, {converted}";
                if (vectorLocals.Contains(converted))
                    return $"VecUnpack({converted})";
            }
            return converted;
        }

        private static string ConvertDrop(Drop drop)
        {
            object? dropped = GetPrivateField(drop, "Dropped");
            if (dropped is AstToken tok)
                return ConvertStatement(tok.ToString());
            return $"-- TODO Drop unsupported: dropped={dropped?.GetType().FullName}, text={drop}";
        }

        private static object? GetPrivateField(object obj, string field)
        {
            return obj.GetType().GetField(field, BindingFlags.Instance | BindingFlags.NonPublic)?.GetValue(obj);
        }

        private static string? TryGetMemoryBaseIndex(object? pointerObj)
        {
            if (pointerObj is not AstToken ptr)
                return null;
            string mem = ReplaceMemoryRefs(ptr.ToString(), true);
            var m = Regex.Match(mem, @"^Local\[(.+)\]$");
            return m.Success ? m.Groups[1].Value : null;
        }

        private static string ConvertExpressionFromObject(object obj)
        {
            if (obj is AstToken tok)
                return ConvertExpression(tok);
            return obj.ToString() ?? "";
        }

        private static void EmitRuntimeHelpers(StringBuilder sb)
        {
            sb.AppendLine("-- Vector3 returns are emitted as Lua multi-return x, y, z.");
            sb.AppendLine("function StoreN(mem, base, count, ...)");
            sb.AppendLine("    local values = {...}");
            sb.AppendLine("    for i = 1, count do");
            sb.AppendLine("        mem[base + (i - 1)] = values[i]");
            sb.AppendLine("    end");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function StoreNFromMemRef(dstRef, dstOffset, count, srcMem, srcBase)");
            sb.AppendLine("    for n = 0, count - 1 do RefSet(dstRef, srcMem[srcBase + n], dstOffset + n) end");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function StoreNRef(ref, offset, count, ...)");
            sb.AppendLine("    local values = {...}");
            sb.AppendLine("    for i = 1, count do");
            sb.AppendLine("        RefSet(ref, values[i], offset + (i - 1))");
            sb.AppendLine("    end");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function StructVar(count, first)");
            sb.AppendLine("    local t = { __struct = true, __count = count }");
            sb.AppendLine("    t[0] = first or 0");
            sb.AppendLine("    for i = 1, count - 1 do t[i] = 0 end");
            sb.AppendLine("    return t");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function StructAssign(mem, base, value, count)");
            sb.AppendLine("    if type(value) == \"table\" then");
            sb.AppendLine("        for k, v in pairs(value) do");
            sb.AppendLine("            if type(k) == \"number\" then");
            sb.AppendLine("                mem[base + k] = v");
            sb.AppendLine("            else");
            sb.AppendLine("                mem[base] = mem[base] or {}");
            sb.AppendLine("                mem[base][k] = v");
            sb.AppendLine("            end");
            sb.AppendLine("        end");
            sb.AppendLine("    else");
            sb.AppendLine("        mem[base] = value");
            sb.AppendLine("    end");
            sb.AppendLine("    return value");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function LocalRef(index)");
            sb.AppendLine("    return { get = function() return Local[index] end, set = function(value) Local[index] = value end, index = index, mem = Local }");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function GlobalRef(index)");
            sb.AppendLine("    return { get = function() return Global[index] end, set = function(value) Global[index] = value end, index = index, mem = Global }");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function StructRef(s, offset)");
            sb.AppendLine("    return { get = function() return s[offset] end, set = function(value) s[offset] = value end, struct = s, offset = offset }");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function StructUnpack(s, count)");
            sb.AppendLine("    if type(s) == \"table\" and s.__struct then");
            sb.AppendLine("        local out = {}");
            sb.AppendLine("        for i = 0, count - 1 do out[#out + 1] = s[i] or 0 end");
            sb.AppendLine("        return table.unpack(out)");
            sb.AppendLine("    end");
            sb.AppendLine("    local out = {s}");
            sb.AppendLine("    for i = 2, count do out[i] = 0 end");
            sb.AppendLine("    return table.unpack(out)");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function VarRef(getter, setter)");
            sb.AppendLine("    return { get = getter, set = setter, isVarRef = true }");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function BitAnd(a, b)");
            sb.AppendLine("    if bit32 and bit32.band then return bit32.band(a, b) end");
            sb.AppendLine("    if bit and bit.band then return bit.band(a, b) end");
            sb.AppendLine("    return 0 -- fallback when no bit library is present");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function RefGet(ref, offset)");
            sb.AppendLine("    offset = offset or 0");
            sb.AppendLine("    return ref.mem[ref.index + offset]");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function RefSet(ref, value, offset)");
            sb.AppendLine("    offset = offset or 0");
            sb.AppendLine("    ref.mem[ref.index + offset] = value");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function RefAt(ref, offset)");
            sb.AppendLine("    return { get = function() return RefGet(ref, offset) end, set = function(value) RefSet(ref, value, offset) end, index = ref.index + offset, mem = ref.mem }");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function RefN(ref, offset, count)");
            sb.AppendLine("    local out = {}");
            sb.AppendLine("    for i = 1, count do out[i] = RefGet(ref, (offset or 0) + (i - 1)) end");
            sb.AppendLine("    return table.unpack(out)");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function Vec3(x, y, z)");
            sb.AppendLine("    if type(x) == \"table\" and x.__vec3 then return Vec3(x.x, x.y, x.z) end");
            sb.AppendLine("    return { __vec3 = true, x = x or 0.0, y = y or 0.0, z = z or 0.0 }");
            sb.AppendLine("end");
            sb.AppendLine();
            sb.AppendLine("function VecUnpack(v)");
            sb.AppendLine("    if type(v) == \"table\" and v.__vec3 then return v.x, v.y, v.z end");
            sb.AppendLine("    return v, nil, nil");
            sb.AppendLine("end");
            sb.AppendLine();
        }


        private static MemoryAddress TryResolveMemoryAddress(string expr)
        {
            string e = expr.Trim();
            var mRef = Regex.Match(e, @"^([A-Za-z_]\w*)->(.*)$");
            if (mRef.Success)
            {
                var off = ParseOffset(mRef.Groups[2].Value);
                return new MemoryAddress(MemoryKind.Ref, mRef.Groups[1].Value, "0", off, true);
            }

            var mG = Regex.Match(e, @"^Global_(\d+)(.*)$");
            if (mG.Success)
            {
                var off = mG.Groups[1].Value + ParseOffset(mG.Groups[2].Value, prependPlus:true);
                return new MemoryAddress(MemoryKind.Global, "Global", "0", off, true);
            }

            var mL = Regex.Match(e, @"^[a-zA-Z]+Local_(\d+)(.*)$");
            if (mL.Success)
            {
                var off = mL.Groups[1].Value + ParseOffset(mL.Groups[2].Value, prependPlus:true);
                return new MemoryAddress(MemoryKind.Local, "Local", "0", off, true);
            }

            var mStruct = Regex.Match(e, @"^([A-Za-z_]\w*)\.(.*)$");
            if (mStruct.Success && mStruct.Groups[2].Value.StartsWith("f_"))
            {
                var off = ParseOffset("." + mStruct.Groups[2].Value).TrimStart().TrimStart('+').Trim();
                return new MemoryAddress(MemoryKind.StructLocal, mStruct.Groups[1].Value, "0", off, true);
            }

            return new MemoryAddress(MemoryKind.Unknown, "", "", expr, false);
        }

        private static string ParseOffset(string suffix, bool prependPlus=false)
        {
            string rem = suffix;
            List<string> parts = new();
            foreach (Match f in Regex.Matches(rem, @"\.f_(\d+)")) parts.Add(f.Groups[1].Value);
            foreach (Match a in Regex.Matches(rem, @"\[(.*?)\]"))
            {
                string inside=a.Groups[1].Value.Trim();
                var sm=Regex.Match(inside,@"^(.*?)\s*/\*\s*(\d+)\s*\*/\s*$");
                if(sm.Success) parts.Add($"({sm.Groups[1].Value.Trim()} * {sm.Groups[2].Value.Trim()})");
                else parts.Add(inside);
            }
            if(parts.Count==0) return "";
            return (prependPlus?" + ":"") + string.Join(" + ", parts);
        }

        private static string EmitMemoryRead(MemoryAddress a) => a.Kind switch
        {
            MemoryKind.Local => $"Local[{a.OffsetExpr}]",
            MemoryKind.Global => $"Global[{a.OffsetExpr}]",
            MemoryKind.Ref => $"RefGet({a.BaseName}, {a.OffsetExpr.TrimStart('+',' ')})",
            MemoryKind.StructLocal => $"{a.BaseName}[{a.OffsetExpr.TrimStart('+',' ')}]",
            _ => a.OffsetExpr
        };
        private static string EmitMemoryWrite(MemoryAddress a, string value) => a.Kind switch
        {
            MemoryKind.Local => $"Local[{a.OffsetExpr}] = {value}",
            MemoryKind.Global => $"Global[{a.OffsetExpr}] = {value}",
            MemoryKind.Ref => $"RefSet({a.BaseName}, {value}, {a.OffsetExpr.TrimStart('+',' ')})",
            MemoryKind.StructLocal => $"{a.BaseName}[{a.OffsetExpr.TrimStart('+',' ')}] = {value}",
            _ => $"-- TODO memory write unsupported: {value}"
        };
        private static string EmitMemoryRef(MemoryAddress a) => a.Kind switch
        {
            MemoryKind.Local => $"LocalRef({a.OffsetExpr})",
            MemoryKind.Global => $"GlobalRef({a.OffsetExpr})",
            MemoryKind.Ref => $"RefAt({a.BaseName}, {a.OffsetExpr.TrimStart('+',' ')})",
            MemoryKind.StructLocal => $"StructRef({a.BaseName}, {a.OffsetExpr.TrimStart('+',' ')})",
            _ => a.OffsetExpr
        };

        private static string NormalizeResolvedArtifacts(string input)
        {
            string o = input;
            o = Regex.Replace(o, @"\b([A-Za-z_]\w+)\.f_(\d+)\[(.*?)\]", m => $"{m.Groups[1].Value}[{m.Groups[2].Value} + {ConvertInlineArrayIndex(m.Groups[3].Value)}]");
            o = Regex.Replace(o, @"\b([A-Za-z_]\w+)\.f_(\d+)", "$1[$2]");
            o = Regex.Replace(o, @"Global\[([^\]]+)\]\.f_(\d+)\[(.*?)\]", m => $"Global[{m.Groups[1].Value} + {m.Groups[2].Value} + {ConvertInlineArrayIndex(m.Groups[3].Value)}]");
            o = Regex.Replace(o, @"Global\[([^\]]+)\]\.f_(\d+)", "Global[$1 + $2]");
            o = Regex.Replace(o, @"Local\[([^\]]+)\]\.f_(\d+)\[(.*?)\]", m => $"Local[{m.Groups[1].Value} + {m.Groups[2].Value} + {ConvertInlineArrayIndex(m.Groups[3].Value)}]");
            o = Regex.Replace(o, @"Local\[([^\]]+)\]\.f_(\d+)", "Local[$1 + $2]");
            o = Regex.Replace(o, @"RefGet\(([^\)]*)\)\.f_(\d+)\[(.*?)\]", m => $"RefGet({m.Groups[1].Value}, {m.Groups[2].Value} + {ConvertInlineArrayIndex(m.Groups[3].Value)})");
            o = Regex.Replace(o, @"RefGet\(([^\)]*)\)\[(.*?)\]", m => $"RefGet({m.Groups[1].Value}, {ConvertInlineArrayIndex(m.Groups[2].Value)})");
            o = Regex.Replace(o, @"RefGet\(([^\)]*),\s*([^\)]*)\)\.f_(\d+)\[(.*?)\]", m => $"RefGet({m.Groups[1].Value}, {m.Groups[2].Value} + {m.Groups[3].Value} + {ConvertInlineArrayIndex(m.Groups[4].Value)})");
            o = Regex.Replace(o, @"VarRef\(function\(\) return ([A-Za-z_]\w+) end, function\(v\) \1 = v end\)\.f_(\d+)\[(.*?)\]", m => $"StructRef({m.Groups[1].Value}, {m.Groups[2].Value} + {ConvertInlineArrayIndex(m.Groups[3].Value)})");
            o = Regex.Replace(o, @"VarRef\(function\(\) return ([A-Za-z_]\w+) end, function\(v\) \1 = v end\)\.f_(\d+)", "StructRef($1, $2)");
            return o;
        }
        private static string[] BuildWarnings(string text)
        {
            List<string> w = new();
            if (text.Contains("->")) w.Add("->");
            if (text.Contains("/*")) w.Add("/*");
            if (text.Contains("&")) w.Add("&");
            if (Regex.IsMatch(text, @"RefGet\([^\)]*\)\s*=")) w.Add("RefGet() =");
            if (Regex.IsMatch(text, @"RefGet\([^\)]*\)\s*\[")) w.Add("RefGet(...)[");
            if (Regex.IsMatch(text, @"RefGet\([^\)]*\)\.")) w.Add("RefGet(...).");
            if (Regex.IsMatch(text, @"Global\[[^\]]+\]\.")) w.Add("Global[...].");
            if (Regex.IsMatch(text, @"Local\[[^\]]+\]\.")) w.Add("Local[...].");
            if (Regex.IsMatch(text, @"for\s+\w+\s*=\s*[^\n]*,\s*=")) w.Add("for i = 0, =");
            if (text.Contains(".f_")) w.Add(".f_");
            return w.ToArray();
        }

        private static void AppendLine(StringBuilder sb, int indent, string text)
        {
            sb.Append(new string(' ', indent * 4));
            sb.AppendLine(text);
        }

        private static string SanitizeTodoText(string text)
        {
            return text.Replace("->", ".").Replace("/*", "[").Replace("*/", "]").Replace("&", "@");
        }
    }
}
