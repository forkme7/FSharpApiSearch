module FSharpApiSearch.Printer

open System.Text
open System
open System.IO

type IPrinter =
  abstract Write : string -> unit
  abstract WriteLine : string -> unit
  abstract WriteLine : unit -> unit
  abstract WriteType : LowType -> unit

module internal PrinterExtensions =
  type IPrinter with
    member this.Append(value: string) : IPrinter = this.Write(value); this

    member this.Append(print: IPrinter -> IPrinter) : IPrinter = print this
    member this.AppendJoin(sep: string, xs: 'a seq, print: 'a -> IPrinter -> IPrinter) : IPrinter =
      if Seq.isEmpty xs then
        this
      else
        let first = ref true

        for x in xs do
          if !first then
            this.Append(print x) |> ignore
            first := false
          else
            this.Append(sep).Append(print x) |> ignore
        this

    member this.AppendJoin(sep: string, xs: string seq) : IPrinter = this.AppendJoin(sep, xs, (fun x sb -> sb.Append(x)))

    member this.PrintType(t: LowType) : IPrinter = this.WriteType(t); this

open PrinterExtensions

type IPrinterHandler<'T> =
  abstract BeginPrintType : 'T -> unit
  abstract EndPrintType : 'T -> unit

type NullHandler<'T>() =
  interface IPrinterHandler<'T> with
    member this.BeginPrintType _ = ()
    member this.EndPrintType _ = ()

[<AbstractClass>]
type PrinterBase<'Writer when 'Writer :> TextWriter>(writer: 'Writer, handler: IPrinterHandler<'Writer>) =
  abstract WriteType : LowType -> unit
  interface IPrinter with
    member this.Write(value: string) = writer.Write(value)
    member this.WriteLine(value: string) = writer.WriteLine(value)
    member this.WriteLine() = writer.WriteLine()
    member this.WriteType(t) =
      handler.BeginPrintType(writer)
      this.WriteType(t)
      handler.EndPrintType(writer)

module internal FSharpImpl =
  open SpecialTypes

  let printPropertyKind = function
    | PropertyKind.Get -> "get"
    | PropertyKind.Set -> "set"
    | PropertyKind.GetSet -> "get set"
  let printMemberKind = function
    | MemberKind.Method -> "method"
    | MemberKind.Property p -> "property with " + printPropertyKind p
    | MemberKind.Field -> "field"
  let printMemberModifier = function
    | MemberModifier.Instance -> "instance"
    | MemberModifier.Static -> "static"
  let printApiKind kind (p: IPrinter) =
    match kind with
    | ApiKind.ModuleValue -> p.Append("module value")
    | ApiKind.Constructor -> p.Append("constructor")
    | ApiKind.Member (modifier, memberKind) -> p.Append(printMemberModifier modifier).Append(" ").Append(printMemberKind memberKind)
    | ApiKind.TypeExtension (modifier, memberKind) -> p.Append(printMemberModifier modifier).Append(" ").Append(printMemberKind memberKind)
    | ApiKind.ExtensionMember -> p.Append("extension member")
    | ApiKind.UnionCase -> p.Append("union case")
    | ApiKind.ModuleDefinition -> p.Append("module")
    | ApiKind.TypeDefinition -> p.Append("type")
    | ApiKind.TypeAbbreviation -> p.Append("type abbreviation")
    | ApiKind.ComputationExpressionBuilder -> p.Append("builder")

  let typeVariablePrefix (v: TypeVariable) = if v.IsSolveAtCompileTime then "^" else "'"

  let toDisplayName = function
    | SymbolName n -> n
    | OperatorName (n, _) -> n
    | WithCompiledName (n, _) -> n

  let printNameItem (n: DisplayNameItem) (p: IPrinter) =
    match n.GenericParameters with
    | [] -> p.Append(toDisplayName n.Name)
    | args ->
      p.Append(toDisplayName n.Name)
        .Append("<")
          .AppendJoin(", ", args, (fun arg p -> p.Append(typeVariablePrefix arg).Append(arg.Name)))
        .Append(">")

  let printDisplayName_full xs (p: IPrinter) =
    match xs with
    | [] -> p.Append("<empty>")
    | ns ->
      ns.Tail
      |> Seq.rev
      |> Seq.iter (fun n -> p.Append(printNameItem n).Append(".") |> ignore)
      p.Append(toDisplayName ns.Head.Name)

  let printName_full (name: Name) (p: IPrinter) =
    let print (name: DisplayName) (p: IPrinter) = p.AppendJoin(".", List.rev name, printNameItem)
    match name with
    | LoadingName (_, n1, n2) ->
      match n2 with
      | [] -> p.Append(n1)
      | n2 ->
        p.Append(n1).Append(".").Append(print n2)
    | DisplayName n -> p.Append(print n)

  let printApiName (name: Name) (p: IPrinter) =
    let name = Name.toDisplayName name
    p.Append(printNameItem name.Head)

  let printAccessPath depth (name: Name) (p: IPrinter) =
    let ns = Name.toDisplayName name
    let depth = Option.defaultValue (ns.Tail.Length) depth
    
    let pathes = List.truncate depth ns.Tail |> List.rev
    p.AppendJoin(".", pathes, printNameItem)

  let printIdentity_full (identity: Identity) (p: IPrinter) =
    match identity with
    | FullIdentity i -> p.Append(printName_full i.Name)
    | PartialIdentity i -> p.Append(printDisplayName_full i.Name)

  let printIdentity_short (identity: Identity) (p: IPrinter) =
    let printDisplayName_short (xs: DisplayName) (p: IPrinter) =
      match xs with
      | [] -> p.Append("<empty>")
      | n :: _ -> p.Append(toDisplayName n.Name)

    let printName_short name (p: IPrinter) =
      match name with
      | LoadingName (_, n1, n2) ->
        match n2 with
        | [] -> p.Append(n1)
        | n2 -> p.Append(printDisplayName_short n2)
      | DisplayName n -> p.Append(printDisplayName_short n)
    
    match identity with
    | FullIdentity i -> p.Append(printName_short i.Name)
    | PartialIdentity i -> p.Append(printDisplayName_short i.Name)

  let printVariableSource = function
    | VariableSource.Query -> "q"
    | VariableSource.Target -> "t"

  let printTypeVariable isDebug source v (p: IPrinter) =
    if isDebug then
      p.Append(typeVariablePrefix v).Append(printVariableSource source).Append("_").Append(v.Name)
    else
      p.Append(typeVariablePrefix v).Append(v.Name)

  let rec printLowType isDebug (printIdentity: Identity -> IPrinter -> IPrinter) lowType (p: IPrinter) =
    match lowType with
    | Wildcard name ->
      match name with
      | Some n -> p.Append("?").Append(n)
      | None -> p.Append("?")
    | Variable (source, v) -> p.Append(printTypeVariable isDebug source v)
    | Identity i -> p.Append(printIdentity i)
    | Arrow xs -> p.Append(printArrow isDebug printIdentity xs)
    | Tuple { Elements = xs; IsStruct = false } -> p.Append(printTuple isDebug printIdentity xs)
    | Tuple { Elements = xs; IsStruct = true } -> p.Append(printStructTuple isDebug printIdentity xs)
    | LowType.Patterns.Array (name, elem) ->
      match elem with
      | Tuple { IsStruct = false } | Arrow _ ->
        p.Append("(")
          .Append(printLowType isDebug printIdentity elem)
          .Append(")")
          |> ignore
      | _ -> p.Append(printLowType isDebug printIdentity elem) |> ignore
      p.Append(name)
    | Generic (id, args) -> p.Append(printGeneric isDebug printIdentity id args)
    | TypeAbbreviation t -> p.Append(printLowType isDebug printIdentity t.Abbreviation)
    | Delegate (t, _) -> p.Append(printLowType isDebug printIdentity t)
    | ByRef (_, t) -> p.Append("byref<").Append(printLowType isDebug printIdentity t).Append(">")
    | Choice xs -> p.Append(printChoice isDebug printIdentity xs)
  and printGeneric isDebug printIdentity id (args: _ list) (p: IPrinter) =
    p.Append(printLowType isDebug printIdentity id)
      .Append("<")
      .AppendJoin(", ", args, (printLowType isDebug printIdentity))
      .Append(">")
  and printArrow isDebug printIdentity (xs: _ list) (p: IPrinter) =
    let printItem lowType (p: IPrinter) =
      match lowType with
      | Arrow _ as a ->
        p.Append("(")
          .Append(printLowType isDebug printIdentity a)
          .Append(")")
      | x -> p.Append(printLowType isDebug printIdentity x)
    p.AppendJoin(" -> ", xs, printItem)
  and printTuple isDebug printIdentity (xs: _ list) (p: IPrinter) =
    let printItem lowType (p: IPrinter) =
      match lowType with
      | Tuple _ as t ->
        p.Append("(")
          .Append(printLowType isDebug printIdentity t)
          .Append(")")
      | x -> p.Append(printLowType isDebug printIdentity x)
    p.AppendJoin(" * ", xs, printItem)
  and printStructTuple isDebug printIdentity (xs: _ list) (p: IPrinter) =
    let printItem lowType (p: IPrinter) =
      match lowType with
      | Tuple { IsStruct = false  } | Arrow _ ->
        p.Append("(")
          .Append(printLowType isDebug printIdentity lowType)
          .Append(")")
      | _ -> p.Append(printLowType isDebug printIdentity lowType)
    p.Append("struct (")
      .AppendJoin(" * ", xs, printItem)
      .Append(")")
  and printChoice isDebug printIdentity (xs: _ list) (p: IPrinter) =
    p.Append("(")
      .AppendJoin(" or ", xs, printLowType isDebug printIdentity)
      .Append(")")

  let printLowType_short isDebug t (p: IPrinter) = p.Append(printLowType isDebug printIdentity_short t)
  let printLowType_full isDebug t (p: IPrinter) = p.Append(printLowType isDebug printIdentity_full t)

  let printParameter tupleParen isDebug (parameter: Parameter) (p: IPrinter) =
    match parameter.IsOptional with
    | true -> p.Append("?") |> ignore
    | false -> ()

    match parameter.Name with
    | Some name -> p.Append(name).Append(":") |> ignore
    | None -> ()

    match parameter with
    | { Type = Tuple _ } when tupleParen ->
      p.Append("(")
        .PrintType(parameter.Type)
        .Append(")")
    | { Type = Arrow _ } ->
      p.Append("(")
        .PrintType(parameter.Type)
        .Append(")")
    | _ -> p.PrintType(parameter.Type)

  let printParameterGroups tupleParen isDebug (func: Parameter list list) (p: IPrinter) =
    p.AppendJoin(" -> ", func, (fun ps p -> p.AppendJoin(" * ", ps, printParameter tupleParen isDebug)))

  let printMember isDebug (m: Member) (p: IPrinter) =
    match m.Parameters with
    | [] -> p.PrintType(m.ReturnParameter.Type)
    | _ ->
      p.Append(printParameterGroups true isDebug m.Parameters)
        .Append(" -> ")
        .PrintType(m.ReturnParameter.Type)

  let printConstraint isDebug (c: TypeConstraint) (p: IPrinter) =
    let variableSource = VariableSource.Target

    match c.Variables with
    | [ v ] ->
      p.Append(printTypeVariable isDebug variableSource v) |> ignore
    | vs ->
      p.Append("(")
        .AppendJoin(" or ", vs, printTypeVariable isDebug variableSource)
        .Append(")")
      |> ignore

    p.Append(" ") |> ignore

    match c.Constraint with
    | Constraint.SubtypeConstraints s ->
      p.Append(":> ")
        .Append(printLowType_short isDebug s)
    | Constraint.NullnessConstraints -> p.Append(": null")
    | Constraint.MemberConstraints (modifier, member') ->
      let printMemberModifier modifier (p: IPrinter) =
        match modifier with
        | MemberModifier.Static -> p.Append("static member")
        | MemberModifier.Instance -> p.Append("member")
      p.Append(": (")
          .Append(printMemberModifier modifier)
          .Append(" ").Append(member'.Name).Append(" : ")
          .Append(printMember isDebug member')
        .Append(")")
    | Constraint.DefaultConstructorConstraints ->
      p.Append(": (new : unit -> ")
        .Append(printTypeVariable isDebug variableSource (c.Variables.Head))
        .Append(")")
    | Constraint.ValueTypeConstraints -> p.Append(": struct")
    | Constraint.ReferenceTypeConstraints -> p.Append(": not struct")
    | Constraint.EnumerationConstraints -> p.Append(": enum")
    | Constraint.DelegateConstraints -> p.Append(": delegate")
    | Constraint.UnmanagedConstraints -> p.Append(": unmanaged")
    | Constraint.EqualityConstraints -> p.Append(": equality")
    | Constraint.ComparisonConstraints -> p.Append(": comparison")
    
  let printFullTypeDefinition isDebug (x: FullTypeDefinition) (p: IPrinter) =
    p.Append("type ")
      .PrintType(x.LowType)

  let pringTypeAbbreviation isDebug (x: TypeAbbreviationDefinition) (p: IPrinter) =
    p.Append("type ")
      .PrintType(x.TypeAbbreviation.Abbreviation)
      .Append(" = ")
      .Append(printLowType_full isDebug x.Abbreviated)

  let printUnionCaseField isDebug (uc: UnionCaseField) (p: IPrinter) =
    match uc.Name with
    | Some name ->
      p.Append(name).Append(":").PrintType(uc.Type)
    | None -> p.PrintType(uc.Type)

  let printUnionCase isDebug (uc: UnionCase) (p: IPrinter) =
    if uc.Fields.IsEmpty then
      p.PrintType(uc.DeclaringType)
    else
      p.Append(printParameterGroups true isDebug (UnionCase.toFunction uc))

  let printModule (m: ModuleDefinition) (p: IPrinter) = p.Append("module ").Append(toDisplayName m.Name.Head.Name)

  let printComputationExpressionBuilder isDebug (builder: ComputationExpressionBuilder) (p: IPrinter) =
    if isDebug then
      p.Append("type ")
        .PrintType(builder.BuilderType)
        .Append(", [ ")
        .AppendJoin("; ", builder.ComputationExpressionTypes, printLowType_short isDebug)
        .Append(" ], { ")
        .AppendJoin("; ", builder.Syntaxes, (fun syntax p -> p.Append(syntax)))
        .Append(" }")
    else
      p.Append("type ")
        .PrintType(builder.BuilderType)
        .Append(", { ")
        .AppendJoin("; ", builder.Syntaxes, (fun syntax p -> p.Append(syntax)))
        .Append(" }")

  let printApiSignature isDebug apiSig (p: IPrinter) =
    match apiSig with
    | ApiSignature.ModuleValue t -> p.PrintType(t)
    | ApiSignature.ModuleFunction fn -> p.Append(printParameterGroups false isDebug fn)
    | ApiSignature.ActivePatten (_, fn) -> p.Append(printParameterGroups false isDebug fn)
    | ApiSignature.InstanceMember (declaringType, m) ->
      if isDebug then
        p.Append(printLowType_short isDebug declaringType)
          .Append(" => ")
          .Append(printMember isDebug m)
      else
        p.Append(printMember isDebug m)
    | ApiSignature.StaticMember (_, m) -> p.Append(printMember isDebug m)
    | ApiSignature.Constructor (_, m) -> p.Append(printMember isDebug m)
    | ApiSignature.ModuleDefinition m -> p.Append(printModule m)
    | ApiSignature.FullTypeDefinition x -> p.Append(printFullTypeDefinition isDebug x)
    | ApiSignature.TypeAbbreviation t -> p.Append(pringTypeAbbreviation isDebug t)
    | ApiSignature.TypeExtension t ->
      if isDebug then
        p.Append(printLowType_short isDebug t.ExistingType)
          .Append(" => ")
          .Append(printMember isDebug t.Member)
      else
        p.Append(printMember isDebug t.Member)
    | ApiSignature.ExtensionMember m -> p.Append(printMember isDebug m)
    | ApiSignature.UnionCase uc -> p.Append(printUnionCase isDebug uc)
    | ApiSignature.ComputationExpressionBuilder builder -> p.Append(printComputationExpressionBuilder isDebug builder)

type FSharpPrinter<'Writer when 'Writer :> TextWriter>(writer, handler) =
  inherit PrinterBase<'Writer>(writer, handler)
  override this.WriteType(t: LowType) = FSharpImpl.printLowType_short false t this |> ignore

module FSharp =
  let printer writer handler = FSharpPrinter<_>(writer, handler) :> IPrinter
  let printAsString (f: IPrinter -> IPrinter) =
    let sb = StringBuilder()
    let printer = printer (new StringWriter(sb)) (NullHandler())
    f printer |> ignore
    sb.ToString()

  let printFullName (p: IPrinter) (api: Api) = p.Append(FSharpImpl.printName_full api.Name) |> ignore
  let printApiName (p: IPrinter) (api: Api) = p.Append(FSharpImpl.printApiName api.Name) |> ignore
  let printAccessPath (p: IPrinter) (depth: int option) (api: Api) = p.Append(FSharpImpl.printAccessPath depth api.Name) |> ignore

  let printSignature (p: IPrinter) (api: Api) = p.Append(FSharpImpl.printApiSignature false api.Signature) |> ignore
  let printKind (p: IPrinter) (api: Api) =
    match api.Signature with
    | ApiSignature.TypeExtension { Declaration = declaration } ->
      p.Append(FSharpImpl.printApiKind api.Kind)
        .Append(" (").Append(FSharpImpl.printDisplayName_full declaration).Append(")")
        |> ignore
    | _ -> p.Append(FSharpImpl.printApiKind api.Kind) |> ignore

  let printTypeConstraints (p: IPrinter) (api: Api) =
    match api.TypeConstraints with
    | [] -> ()
    | xs ->
      p.Append("when ")
        .AppendJoin(" and ", xs, FSharpImpl.printConstraint false)
        |> ignore

module internal CSharpImpl =
  open SpecialTypes.LowType.Patterns

  let toDisplayName = function
    | SymbolName n -> n
    | OperatorName (_, n) -> n
    | WithCompiledName (_, n) -> n

  let printNameItem (n: DisplayNameItem) (sb: StringBuilder) =
    match n.GenericParameters with
    | [] -> sb.Append(toDisplayName n.Name)
    | args ->
      sb.Append(toDisplayName n.Name)
        .Append("<")
          .AppendJoin(", ", args, (fun arg sb -> sb.Append(arg.Name)))
        .Append(">")

  let printDisplayName_full xs (sb: StringBuilder) = sb.AppendJoin(".", List.rev xs, printNameItem)

  let printName_full (name: Name) (sb: StringBuilder) =
    match name with
    | LoadingName (_, n1, n2) ->
      match n2 with
      | [] -> sb.Append(n1)
      | n2 ->
        sb.Append(n1).Append(".").Append(printDisplayName_full n2)
    | DisplayName n -> sb.Append(printDisplayName_full n)

  let printApiName (name: Name) (sb: StringBuilder) =
    let name = Name.toDisplayName name
    sb.Append(printNameItem name.Head)

  let printAccessPath depth (name: Name) (sb: StringBuilder) =
    let ns = Name.toDisplayName name
    let depth = Option.defaultValue (ns.Tail.Length) depth
    
    let pathes = List.truncate depth ns.Tail |> List.rev
    sb.AppendJoin(".", pathes, printNameItem)

  let csharpAlias =
    SpecialTypes.Identity.CSharp.aliases
    |> List.map (fun (alias, t) ->
      let alias = FullIdentity { AssemblyName = "dummy"; Name = Name.ofString alias; GenericParameterCount = 0 }
      t, alias
    )
    |> dict

  let printIdentity (identity: Identity) (sb: StringBuilder) =
    let identity =
      match csharpAlias.TryGetValue(identity) with
      | true, alias -> alias
      | false, _ -> identity

    let printDisplayName_short (xs: DisplayName) (sb: StringBuilder) =
      match xs with
      | [] -> sb.Append("<empty>")
      | n :: _ -> sb.Append(toDisplayName n.Name)

    let printName_short name (sb: StringBuilder) =
      match name with
      | LoadingName (_, n1, n2) ->
        match n2 with
        | [] -> sb.Append(n1)
        | n2 -> sb.Append(printDisplayName_short n2)
      | DisplayName n -> sb.Append(printDisplayName_short n)
    
    match identity with
    | FullIdentity i -> sb.Append(printName_short i.Name)
    | PartialIdentity i -> sb.Append(printDisplayName_short i.Name)

  let toFSharpFunc xs = xs |> List.reduceBack (fun id ret -> Generic(SpecialTypes.LowType.FSharpFunc, [ id; ret ]))

  let rec nestedArray acc = function
    | Array (name, elem) -> nestedArray (name :: acc) elem
    | x -> acc, x

  let printRef isOut = if isOut then "out" else "ref"

  let rec printLowType t (sb: StringBuilder) =
    match t with
    | Wildcard name ->
      match name with
      | Some n -> sb.Append("?").Append(n)
      | None -> sb.Append("?")
    | Variable (_, v) -> sb.Append(v.Name)
    | Identity i -> sb.Append(printIdentity i)
    | Arrow xs -> printLowType (toFSharpFunc xs) sb
    | Tuple { Elements = xs; IsStruct = false } -> sb.Append("Tuple<").AppendJoin(", ", xs, printLowType).Append(">")
    | Tuple { Elements = xs; IsStruct = true } -> sb.Append("(").AppendJoin(", ", xs, printLowType).Append(")")
    | Array (array, elem) ->
      let arrays, elem = nestedArray [ array ] elem
      sb.Append(printLowType elem) |> ignore
      arrays |> Seq.rev |> Seq.iter (fun a -> sb.Append(a) |> ignore)
      sb
    | Generic (id, args) -> sb.Append(printLowType id).Append("<").AppendJoin(", ", args, printLowType).Append(">")
    | TypeAbbreviation t -> sb.Append(printLowType t.Original)
    | Delegate (t, _) -> sb.Append(printLowType t)
    | ByRef (isOut, t) -> sb.Append(printRef isOut).Append(" ").Append(printLowType t)
    | Choice xs -> sb.Append("(").AppendJoin(" or ", xs, printLowType).Append(")")

  let printParameter (p: Parameter) (sb: StringBuilder) =
    sb.Append(printLowType p.Type) |> ignore
    p.Name |> Option.iter (fun name -> sb.Append(" ").Append(name) |> ignore)
    sb

  let printPropertyParameter (m: Member) (sb: StringBuilder) =
    let parameters = m.Parameters |> List.collect id
    sb.Append("[").AppendJoin(", ", parameters, printParameter).Append("]")

  let printProperty (m: Member) (sb: StringBuilder) =
    if List.isEmpty m.Parameters = false then sb.Append(printPropertyParameter m) |> ignore
    sb.Append(" : ").Append(printLowType m.ReturnParameter.Type)

  let printReturnParameter (p: Parameter) (sb: StringBuilder) =
    match p.Type with
    | Unit -> sb.Append("void")
    | t -> sb.Append(printLowType t)

  let printMethodParameter (m: Member) (isExtension: bool) (sb: StringBuilder) =
    let parameters = m.Parameters |> List.collect id
    match parameters with
    | [ { Type = Unit } ] ->
      sb.Append("()")
    | _ ->
      if isExtension then
        sb.Append("(this ") |> ignore
      else
        sb.Append("(") |> ignore
      sb.AppendJoin(", ", parameters, printParameter).Append(")")

  let printMethod (m: Member) (isExtension: bool) (sb: StringBuilder) =
    sb.Append(printMethodParameter m isExtension)
      .Append(" : ")
      .Append(printReturnParameter m.ReturnParameter)

  let printField (m: Member) (sb: StringBuilder) =
    sb.Append(" : ").Append(printLowType m.ReturnParameter.Type)

  let printMember (m: Member) (sb: StringBuilder) =
    match m.Kind with
    | MemberKind.Property _ -> sb.Append(printProperty m)
    | MemberKind.Method -> sb.Append(printMethod m false)
    | MemberKind.Field -> sb.Append(printField m)

  let printConstructor (m: Member) (sb: StringBuilder) =
    sb.Append(printMethodParameter m false).Append(" : void")

  let printModuleValue (t: LowType) (sb: StringBuilder) = sb.Append(" : ").Append(printLowType t)

  let printFunction (fn: Function) (sb: StringBuilder) =
    let m = {
      Name = "dummy"
      Kind = MemberKind.Method
      GenericParameters = []
      Parameters = fn |> List.take (List.length fn - 1)
      ReturnParameter = fn |> List.last |> List.head
    }
    printMethod m false sb

  let printFullTypeDefinition (td: FullTypeDefinition) (sb: StringBuilder) =
    let kind =
      match td.Kind with
      | TypeDefinitionKind.Class
      | TypeDefinitionKind.Record
      | TypeDefinitionKind.Type
      | TypeDefinitionKind.Union -> "class"
      | TypeDefinitionKind.Interface -> "interface"
      | TypeDefinitionKind.Enumeration -> "enum"
    sb.Append(" : ").Append(kind).Append(" ").Append(printNameItem td.Name.[0])

  let printApiSignature (apiSig: ApiSignature) (sb: StringBuilder) =
    let error name = failwithf "%s is not C# api." name
    match apiSig with
    | ApiSignature.ModuleValue t -> sb.Append(printModuleValue t)
    | ApiSignature.ModuleFunction fn -> sb.Append(printFunction fn)
    | ApiSignature.ActivePatten (_, _) -> error "ActivePattern"
    | ApiSignature.InstanceMember (_, m) -> sb.Append(printMember m)
    | ApiSignature.StaticMember (_, m) -> sb.Append(printMember m)
    | ApiSignature.Constructor (_, m) -> sb.Append(printConstructor m)
    | ApiSignature.ModuleDefinition _ -> error "Module"
    | ApiSignature.FullTypeDefinition td -> sb.Append(printFullTypeDefinition td)
    | ApiSignature.TypeAbbreviation _ -> error "TypeAbbreviation"
    | ApiSignature.TypeExtension _ -> error "TypeExtension"
    | ApiSignature.ExtensionMember m -> sb.Append(printMethod m true)
    | ApiSignature.UnionCase _ -> error "UnionCase"
    | ApiSignature.ComputationExpressionBuilder _ -> error "ComputationExpression"

  let filterCSharpTypeConstraint (xs: TypeConstraint list) =
    xs
    |> List.filter (fun x ->
      match x.Constraint with
      | Constraint.NullnessConstraints
      | Constraint.MemberConstraints _
      | Constraint.EnumerationConstraints
      | Constraint.DelegateConstraints
      | Constraint.UnmanagedConstraints
      | Constraint.EqualityConstraints
      | Constraint.ComparisonConstraints -> false

      | Constraint.SubtypeConstraints _
      | Constraint.DefaultConstructorConstraints
      | Constraint.ValueTypeConstraints
      | Constraint.ReferenceTypeConstraints -> true)

  let printConstraint (c: TypeConstraint) (sb: StringBuilder) =
    let print (v: TypeVariable) (sb: StringBuilder) =
      sb.Append("where ").Append(v.Name).Append(" : ") |> ignore

      match c.Constraint with
      | Constraint.SubtypeConstraints s -> sb.Append(printLowType s) |> ignore
      | Constraint.DefaultConstructorConstraints -> sb.Append("new()") |> ignore
      | Constraint.ValueTypeConstraints -> sb.Append("struct") |> ignore
      | Constraint.ReferenceTypeConstraints -> sb.Append("class") |> ignore
      | _ -> failwith "It is not C# constraint."

      sb

    sb.AppendJoin(" ", c.Variables, print)

  let printPropertyKind = function
    | PropertyKind.Get -> "get"
    | PropertyKind.Set -> "set"
    | PropertyKind.GetSet -> "get set"
  let printMemberKind = function
    | MemberKind.Method -> "method"
    | MemberKind.Property p -> "property with " + printPropertyKind p
    | MemberKind.Field -> "field"
  let printMemberModifier = function
    | MemberModifier.Instance -> "instance"
    | MemberModifier.Static -> "static"
  let printApiKind kind (sb: StringBuilder) =
    match kind with
    | ApiKind.ModuleValue -> sb.Append(printMemberModifier MemberModifier.Static).Append(" ").Append(printMemberKind MemberKind.Method)
    | ApiKind.Constructor -> sb.Append("constructor")
    | ApiKind.Member (modifier, memberKind) -> sb.Append(printMemberModifier modifier).Append(" ").Append(printMemberKind memberKind)
    | ApiKind.ExtensionMember -> sb.Append("extension method")
    | ApiKind.TypeDefinition -> sb.Append("type")

    | ApiKind.UnionCase
    | ApiKind.ModuleDefinition
    | ApiKind.TypeAbbreviation
    | ApiKind.ComputationExpressionBuilder
    | ApiKind.TypeExtension _ -> failwith "It is not C# api."

module CSharp =
  let printFullName (api: Api) = StringBuilder().Append(CSharpImpl.printName_full api.Name).ToString()
  let printApiName (api: Api) = StringBuilder().Append(CSharpImpl.printApiName api.Name).ToString()
  let printAccessPath (depth: int option) (api: Api) = StringBuilder().Append(CSharpImpl.printAccessPath depth api.Name).ToString()

  let printSignature (api: Api) = StringBuilder().Append(CSharpImpl.printApiSignature api.Signature).ToString()

  let tryPrintTypeConstraints (api: Api) =
    let xs = api.TypeConstraints |> CSharpImpl.filterCSharpTypeConstraint
    match xs with
    | [] -> None
    | _ -> StringBuilder().AppendJoin(" ", xs, CSharpImpl.printConstraint).ToString() |> Some

  let printKind (api: Api) = StringBuilder().Append(CSharpImpl.printApiKind api.Kind).ToString()

type TypeVariable with
  member this.Print() = FSharp.printAsString (FSharpImpl.printTypeVariable false VariableSource.Target this)

type DisplayNameItem with
  member this.Print() = FSharp.printAsString (FSharpImpl.printNameItem this)

type Name with
  member this.Print() = FSharp.printAsString (FSharpImpl.printName_full this)

type LowType with
  member this.Print() = FSharp.printAsString (FSharpImpl.printLowType_short false this)
  member internal this.Debug() = FSharp.printAsString (FSharpImpl.printLowType_short true this)

type ApiSignature with
  member this.Print() = FSharp.printAsString (FSharpImpl.printApiSignature false this)
  member internal this.Debug() = FSharp.printAsString (FSharpImpl.printApiSignature true this)

type TypeConstraint with
  member this.Print() = FSharp.printAsString (FSharpImpl.printConstraint false this)
  member internal this.Debug() = FSharp.printAsString (FSharpImpl.printConstraint true this)
  
type FullTypeDefinition with
  member this.Print() = FSharp.printAsString (FSharpImpl.printFullTypeDefinition false this)
  member internal this.Debug() = FSharp.printAsString (FSharpImpl.printFullTypeDefinition true this)
  
module internal LowType =
  let debug (x: LowType) = x.Debug()

module internal ApiSignature =
  let debug (x: ApiSignature) = x.Debug()
  let print (x: ApiSignature) = x.Print()
  
module internal TypeConstraint =
  let debug (x: TypeConstraint) = x.Debug()
  
module internal FullTypeDefinition =
  let debug (x: FullTypeDefinition) = x.Debug()