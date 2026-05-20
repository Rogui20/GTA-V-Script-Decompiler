using Decompiler.Ast;
using Decompiler.Ast.StatementTree;
using System;
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

        public string EmitFunction(Function func)
        {
            StringBuilder sb = new();
            sb.AppendLine($"function {func.Name}()") ;
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
            return sb.ToString();
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
                AppendLine(sb, indent, first ? "if true then" : "else");
                EmitTreeBody(sb, defaultCase, indent + 1, true);
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

            string pattern = @"^" + Regex.Escape(varName) + @"\s*<\s*(.+)$";
            var mCond = Regex.Match(cond, pattern);
            if (!mCond.Success)
                return false;

            var mIncr = Regex.Match(incr, @"^" + Regex.Escape(varName) + @"\s*=\s*" + Regex.Escape(varName) + @"\s*\+\s*1(\.0)?$");
            if (!mIncr.Success)
                return false;

            string endExclusive = mCond.Groups[1].Value.Trim();
            AppendLine(sb, indent, $"for {varName} = {startExpr}, {endExclusive} - 1 do");
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
                case NativeCall nativeCall when nativeCall.IsStatement():
                    AppendLine(sb, indent, ConvertNativeStatement(nativeCall));
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
            return ConvertMemoryModel(ConvertOperators(ConvertFloatLiterals(ConvertNamespaces(value.TrimEnd(';')))));
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
            return ConvertMemoryModel(ConvertOperators(ConvertFloatLiterals(ConvertNamespaces(statement.TrimEnd(';')))));
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
            output = Regex.Replace(output, @"&\(([^)]+)\)", "$1");
            output = ReplaceMemoryRefs(output, true);
            output = ReplaceMemoryRefs(output, false);
            return output;
        }

        private static string ReplaceMemoryRefs(string input, bool local)
        {
            string prefix = local ? "Local" : "Global";
            string pat = local ? @"\b[a-zA-Z]+Local_(\d+)((?:\.f_\d+)*)((?:\[[^\]]+\])?)" : @"\bGlobal_(\d+)((?:\.f_\d+)*)((?:\[[^\]]+\])?)";
            return Regex.Replace(input, pat, m =>
            {
                int baseIdx = int.Parse(m.Groups[1].Value);
                int sum = baseIdx;
                foreach (Match fm in Regex.Matches(m.Groups[2].Value, @"\.f_(\d+)"))
                    sum += int.Parse(fm.Groups[1].Value);

                string expr = sum.ToString();
                string arr = m.Groups[3].Value;
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
                return $"{prefix}[{expr}]";
            });
        }

        private void EmitFunctionLocals(StringBuilder sb, Function func, int indent)
        {
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

        private static void AppendLine(StringBuilder sb, int indent, string text)
        {
            sb.Append(new string(' ', indent * 4));
            sb.AppendLine(text);
        }
    }
}
