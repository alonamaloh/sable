import Lean
import Sable

open Lean

private def requestSchema := "sable-proof-ingress-request-v2"
private def resultSchema := "sable-proof-ingress-result-v2"

private structure Fragment where
  category : String
  text : String
  expectedKind : String
  expectedName : String
  expectedModifiers : String

private abbrev RawJsonObject := Std.TreeMap.Raw String Json compare

private def exactObject (json : Json) (fields : Array String) : Except String RawJsonObject := do
  let object ← json.getObj?
  if object.size != fields.size then
    throw s!"expected exactly fields {fields.toList}, got {object.toList.map (fun entry => entry.1)}"
  for field in fields do
    unless object.contains field do
      throw s!"missing required field '{field}'"
  return object

private def parseFragment (json : Json) : Except String Fragment := do
  discard <| exactObject json
    #["category", "text", "expected_kind", "expected_name", "expected_modifiers"]
  return {
    category := ← json.getObjVal? "category" >>= Json.getStr?
    text := ← json.getObjVal? "text" >>= Json.getStr?
    expectedKind := ← json.getObjVal? "expected_kind" >>= Json.getStr?
    expectedName := ← json.getObjVal? "expected_name" >>= Json.getStr?
    expectedModifiers := ← json.getObjVal? "expected_modifiers" >>= Json.getStr?
  }

private def parseRequest (input : String) : Except String (Array Fragment) := do
  let json ← Json.parse input
  discard <| exactObject json #["schema", "fragments"]
  let schema ← json.getObjVal? "schema" >>= Json.getStr?
  unless schema == requestSchema do
    throw s!"unsupported request schema '{schema}'"
  let fragmentsJson ← json.getObjVal? "fragments" >>= Json.getArr?
  fragmentsJson.mapM parseFragment

private def rejectExecutableElaborationSyntax (stx : Syntax) : Except String Unit := do
  for child in stx.topDown do
    if child.isOfKind ``Parser.Term.byElab then
      throw "`by_elab` is not permitted in generated proof fragments"
    if child.isOfKind ``Parser.Tactic.runTac then
      throw "`run_tac` is not permitted in generated proof fragments"

private def validateCommand
    (environment : Environment)
    (fragment : Fragment) : Except String Unit := do
  let stx ← Parser.runParserCategory environment `command fragment.text
  rejectExecutableElaborationSyntax stx
  unless stx.isOfKind ``Parser.Command.declaration do
    throw s!"expected one declaration command, got syntax kind '{stx.getKind}'"
  let some actualModifiers := stx[0].reprint
    | throw "cannot reproduce the declaration's exact modifier syntax"
  unless actualModifiers == fragment.expectedModifiers do
    throw s!"expected declaration modifiers '{fragment.expectedModifiers}', got '{actualModifiers}'"
  let declaration := stx[1]
  let expectedSyntaxKind ← match fragment.expectedKind with
    | "definition" => pure ``Parser.Command.definition
    | "theorem" => pure ``Parser.Command.theorem
    | other => throw s!"unsupported expected declaration kind '{other}'"
  unless declaration.isOfKind expectedSyntaxKind do
    throw s!"expected '{fragment.expectedKind}', got syntax kind '{declaration.getKind}'"
  let (actualName, _) := Elab.expandDeclIdCore declaration[1]
  unless actualName.toString == fragment.expectedName do
    throw s!"expected declaration '{fragment.expectedName}', got '{actualName}'"
  unless declaration[3].isOfKind ``Parser.Command.declValSimple do
    throw "ghost declarations must use one simple `:=` value"
  -- Termination/decreasing suffixes remain available for recursive ghost
  -- definitions, but nested `where` declarations could manufacture siblings.
  unless declaration[3][3].isNone do
    throw "ghost declarations may not contain `where` declarations"
  -- A source-authored `deriving` clause can manufacture sibling declarations.
  -- Sable ghost definitions do not expose that feature; any auxiliaries must
  -- instead be attributable to elaborating the one confined declaration.
  if fragment.expectedKind == "definition" && !declaration[4].isNone then
    throw "ghost definitions may not contain a deriving clause"

private def validateFragment
    (environment : Environment)
    (fragment : Fragment) : Except String Unit := do
  match fragment.category with
  | "command" => validateCommand environment fragment
  | "term" =>
      unless fragment.expectedKind.isEmpty && fragment.expectedName.isEmpty &&
          fragment.expectedModifiers.isEmpty do
        throw "term fragments must not carry declaration expectations"
      let stx ← Parser.runParserCategory environment `term fragment.text
      rejectExecutableElaborationSyntax stx
  | other => throw s!"unsupported fragment category '{other}'"

private def accepted : Json := Json.mkObj [
  ("schema", Json.str resultSchema),
  ("accepted", Json.bool true)
]

private def rejected (kind : String) (message : String) (index? : Option Nat := none) : Json :=
  let base : List (String × Json) := [
    ("schema", Json.str resultSchema),
    ("accepted", Json.bool false),
    ("failure_kind", Json.str kind),
    ("message", Json.str message)
  ]
  let index : List (String × Json) := match index? with
    | some index => [("index", Json.num index)]
    | none => []
  Json.mkObj (base ++ index)

private unsafe def parserEnvironment : IO Environment := do
  -- Only the repository-local, content-hashed Sable prelude is loaded with
  -- extensions. Candidate generated modules are deliberately absent here;
  -- the declaration auditor imports those separately with `loadExts=false`.
  -- Native Lean executables do not initialize the module search path. The
  -- surrounding sanitized `lake env` supplies the authenticated `LEAN_PATH`
  -- and pinned `lean` whose sysroot is discovered here.
  initSearchPath (← findSysroot)
  enableInitializersExecution
  importModules
    #[{ module := `Sable, importAll := true }]
    {}
    (trustLevel := 0)
    (plugins := #[])
    (leakEnv := false)
    (loadExts := true)
    (level := .private)

private unsafe def run : IO Json := do
  let bytes ← (← IO.getStdin).readBinToEnd
  let some input := String.fromUTF8? bytes
    | return rejected "transport" "request stdin is not valid UTF-8"
  match parseRequest input with
  | .error message => return rejected "request" message
  | .ok fragments =>
      let environment ← parserEnvironment
      let mut rejection : Option (Nat × String) := none
      for entry in fragments.zipIdx do
        if rejection.isNone then
          if let .error message := validateFragment environment entry.1 then
            rejection := some (entry.2, message)
      match rejection with
      | some (index, message) => return rejected "fragment" message (some index)
      | none => return accepted

unsafe def main : IO UInt32 := do
  let result ← try
    run
  catch error =>
    pure <| rejected "auditor" error.toString
  IO.println result.compress
  return 0
