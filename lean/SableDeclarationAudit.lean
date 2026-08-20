import Lean

open Lean

/-!
This executable is an observational `ModuleData` inventory probe. It reads one
explicit `.olean` with `Lean.readModuleData` and reports only the serialized
header data already present in that file. It does not import the candidate,
install, replay, or interpret its opaque environment-extension entries, run
its initializers, replay its declarations, or decide whether the candidate is
acceptable.

`readModuleData` is Lean's compacted-region reader, so this probe is intended
only for artifacts produced by the pinned Lean toolchain. The compacted region
is deliberately retained until the process exits.
-/

private def requestSchema := "sable-declaration-inventory-request-v1"
private def resultSchema := "sable-declaration-inventory-result-v1"

private abbrev RawJsonObject := Std.TreeMap.Raw String Json compare

private def exactObject (json : Json) (fields : Array String) : Except String RawJsonObject := do
  let object ← json.getObj?
  if object.size != fields.size then
    throw s!"expected exactly fields {fields.toList}, got {object.toList.map (fun entry => entry.1)}"
  for field in fields do
    unless object.contains field do
      throw s!"missing required field '{field}'"
  return object

private def parseRequest (input : String) : Except String String := do
  let json ← Json.parse input
  unless json.compress == input do
    throw "request must use the exact canonical single-object JSON encoding"
  discard <| exactObject json #["schema", "candidate_olean"]
  let schema ← json.getObjVal? "schema" >>= Json.getStr?
  unless schema == requestSchema do
    throw s!"unsupported request schema '{schema}'"
  let candidate ← json.getObjVal? "candidate_olean" >>= Json.getStr?
  if candidate.isEmpty then
    throw "candidate_olean must be a nonempty UTF-8 path"
  return candidate

/- `Name.toString` is not injective for hygienic names. Preserve the recursive
shape so inventory identity cannot conflate printable names. -/
private def nameJson : Name → Json
  | .anonymous => Json.null
  | .str pre value => Json.mkObj [
      ("str", Json.arr #[nameJson pre, Json.str value])
    ]
  | .num pre value => Json.mkObj [
      ("num", Json.arr #[nameJson pre, Json.num value])
    ]

private def optionalNameJson : Option Name → Json
  | some name => Json.mkObj [("some", nameJson name)]
  | none => Json.null

private def importJson (imp : Import) : Json := Json.mkObj [
  ("module", nameJson imp.module),
  ("import_all", Json.bool imp.importAll),
  ("is_exported", Json.bool imp.isExported),
  ("is_meta", Json.bool imp.isMeta)
]

private def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def constantSafety (info : ConstantInfo) : String :=
  if info.isPartial then "partial" else if info.isUnsafe then "unsafe" else "safe"

private def stringOrNull : Option String → Json
  | some value => Json.str value
  | none => Json.null

private def constantSlotsJson (data : ModuleData) : Json := Id.run do
  let mut slots := #[]
  let slotCount := max data.constNames.size data.constants.size
  for index in [:slotCount] do
    let constName? := data.constNames[index]?
    let info? := data.constants[index]?
    slots := slots.push <| Json.mkObj [
      ("const_name", optionalNameJson constName?),
      ("info_name", optionalNameJson (info?.map ConstantInfo.name)),
      ("kind", stringOrNull (info?.map constantKind)),
      ("safety", stringOrNull (info?.map constantSafety))
    ]
  return Json.arr slots

private def extensionFamilyJson (entry : Name × Array EnvExtensionEntry) : Json := Json.mkObj [
  ("name", nameJson entry.1),
  ("count", Json.num entry.2.size)
]

private def inventory (data : ModuleData) : Json := Json.mkObj [
  ("schema", Json.str resultSchema),
  ("observational", Json.bool true),
  ("is_module", Json.bool data.isModule),
  ("imports", Json.arr (data.imports.map importJson)),
  ("constants", constantSlotsJson data),
  ("extra_const_names", Json.arr (data.extraConstNames.map nameJson)),
  ("extension_families", Json.arr (data.entries.map extensionFamilyJson))
]

private def rejected (kind : String) (message : String) : Json := Json.mkObj [
  ("schema", Json.str resultSchema),
  ("observational", Json.bool true),
  ("error_kind", Json.str kind),
  ("message", Json.str message)
]

private def run : IO Json := do
  let bytes ← (← IO.getStdin).readBinToEnd
  let some input := String.fromUTF8? bytes
    | return rejected "transport" "request stdin is not valid UTF-8"
  match parseRequest input with
  | .error message => return rejected "request" message
  | .ok candidate =>
      let (data, region) ← readModuleData ⟨candidate⟩
      let result := inventory data
      -- `data` points into this compacted region. Do not free it; retaining the
      -- handle through result construction makes the one-shot process lifetime
      -- the storage lifetime.
      let _region := region
      return result

def main : IO UInt32 := do
  let result ← try
    run
  catch error =>
    pure <| rejected "inventory" error.toString
  IO.println result.compress
  return 0
