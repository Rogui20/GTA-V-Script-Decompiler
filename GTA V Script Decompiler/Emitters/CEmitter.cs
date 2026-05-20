using System.Text;

namespace Decompiler.Emitters
{
    /// <summary>
    /// C emitter intentionally preserves the current output behaviour by reusing existing ToString() paths.
    /// </summary>
    internal class CEmitter : IEmitter
    {
        public string EmitFunction(Function func) => func.ToString();

        public string EmitScript(ScriptFile file)
        {
            StringBuilder sb = new();

            if (file.Header.GlobalsCount > 0)
            {
                sb.AppendLine($"// Program registers {file.Header.GlobalsCount & 0x3FFFF} globals at index {file.Header.GlobalsCount >> 18} starting from Global_{0x40000 * (file.Header.GlobalsCount >> 18)}");
            }

            if (Properties.Settings.Default.DeclareVariables)
            {
                if (file.Header.StaticsCount > 0)
                {
                    sb.AppendLine("#region Local Var");
                    foreach (var s in file.Statics.GetDeclaration())
                    {
                        sb.Append('\t');
                        sb.AppendLine(s);
                    }

                    sb.AppendLine("#endregion");
                    sb.AppendLine();
                }
            }

            foreach (var func in file.Functions)
            {
                sb.AppendLine(EmitFunction(func));
            }

            return sb.ToString();
        }
    }
}
