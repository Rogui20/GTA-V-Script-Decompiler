using Decompiler.Ast;
using Decompiler.Ast.StatementTree;
using System;
using System.Text;

namespace Decompiler.Emitters
{
    /// <summary>
    /// Minimal Lua backend prototype.
    /// This is intentionally conservative and only supports a limited subset to prove backend pluggability.
    /// Future expansions should map additional AstToken/Tree types here without touching decode logic.
    /// </summary>
    internal class LuaEmitter : IEmitter
    {
        public string EmitFunction(Function func)
        {
            StringBuilder sb = new();
            sb.AppendLine($"function {func.Name}()") ;
            EmitTreeBody(sb, func.MainTree, 1);
            sb.AppendLine("end");
            return sb.ToString();
        }

        public string EmitScript(ScriptFile file)
        {
            StringBuilder sb = new();
            foreach (var func in file.Functions)
            {
                sb.AppendLine(EmitFunction(func));
            }
            return sb.ToString();
        }

        private void EmitTreeBody(StringBuilder sb, Tree tree, int indent)
        {
            foreach (var statement in tree.Statements)
            {
                EmitNode(sb, statement, indent);
            }
        }

        private void EmitNode(StringBuilder sb, object node, int indent)
        {
            switch (node)
            {
                case If i:
                    EmitIf(sb, i, indent);
                    break;
                case While w:
                    EmitWhile(sb, w, indent);
                    break;
                case AstToken token:
                    EmitTokenStatement(sb, token, indent);
                    break;
                case Tree nested:
                    EmitTreeBody(sb, nested, indent);
                    break;
                default:
                    AppendLine(sb, indent, $"-- TODO unsupported token: {node.GetType().FullName}");
                    break;
            }
        }

        private void EmitIf(StringBuilder sb, If node, int indent)
        {
            AppendLine(sb, indent, $"if {ConvertExpression(node.Condition)} then");
            EmitTreeBody(sb, node, indent + 1);

            foreach (var elseIf in node.ElseIfTrees)
            {
                AppendLine(sb, indent, $"elseif {ConvertExpression(elseIf.Condition)} then");
                EmitTreeBody(sb, elseIf, indent + 1);
            }

            if (node.ElseTree != null)
            {
                AppendLine(sb, indent, "else");
                EmitTreeBody(sb, node.ElseTree, indent + 1);
            }

            AppendLine(sb, indent, "end");
        }

        private void EmitWhile(StringBuilder sb, While node, int indent)
        {
            AppendLine(sb, indent, $"while {ConvertExpression(node.Condition)} do");
            EmitTreeBody(sb, node, indent + 1);
            AppendLine(sb, indent, "end");
        }

        private void EmitTokenStatement(StringBuilder sb, AstToken token, int indent)
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
            return ConvertStatement($"NATIVE.{name}{argsPart}");
        }

        private static string ConvertExpression(AstToken token)
        {
            string value = token is NativeCall native
                ? ConvertNativeExpression(native)
                : token.ToString();
            return ConvertOperators(value.TrimEnd(';'));
        }

        private static string ConvertNativeExpression(NativeCall call)
        {
            string c = call.ToString();
            int paren = c.IndexOf('(');
            string argsPart = paren >= 0 ? c.Substring(paren) : "()";
            string name = call.Name.Replace("::", ".").ToUpperInvariant();
            return $"NATIVE.{name}{argsPart}";
        }

        private static string ConvertStatement(string statement)
        {
            return ConvertOperators(statement.TrimEnd(';'));
        }

        private static string ConvertOperators(string input)
        {
            string output = input.Replace("&&", "and").Replace("||", "or");
            output = output.Replace("!=", "~=");
            output = output.Replace("!", "not ");
            return output;
        }

        private static void AppendLine(StringBuilder sb, int indent, string text)
        {
            sb.Append(new string(' ', indent * 4));
            sb.AppendLine(text);
        }
    }
}
