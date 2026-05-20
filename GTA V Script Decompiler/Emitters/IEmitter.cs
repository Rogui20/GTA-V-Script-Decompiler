namespace Decompiler.Emitters
{
    internal interface IEmitter
    {
        string EmitFunction(Function func);
        string EmitScript(ScriptFile file);
    }
}
