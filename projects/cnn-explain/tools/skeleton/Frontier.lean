/-
审计面（frontier）——由 `mathlean frontier` 生成，不要手改。

它回答一个问题：**这个工程的证明，从工程外面借用了什么？**

做法：从台账里每个 `PROVED` 声明出发，沿着"本项目内部的声明"做传递闭包，
把闭包里每个声明直接引用的常量收集起来，去掉属于本项目的，剩下的就是审计面。

之所以在 Mathlib 边界上停下、不继续展开，是因为那些引理就是"借来的事实"：
它们如果是错的，错在外面，逐条核对它们比展开它们更有意义。
-/

import Lean
import __LIB_IMPORT__

open Lean Elab Command

/-- 要计算审计面的声明（来自台账的 PROVED 行）。 -/
def frontierTargets : List Name := [__TARGETS__]

/-- 本工程自己的模块名。落在这个集合里的声明属于"证明本体"，不进审计面。 -/
def frontierProjectModules : List Name := [__PROJECT_MODULES__]

/-- 输出文件。 -/
def frontierOutputFile : String := "__OUTPUT__"

private def kindOf : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .thmInfo _    => "theorem"
  | .defnInfo _   => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

private def projectIndices (env : Environment) : Std.HashSet Nat := Id.run do
  let mut s : Std.HashSet Nat := ∅
  let modules := env.header.modules
  for h : i in [:modules.size] do
    if frontierProjectModules.contains modules[i].module then
      s := s.insert i
  return s

private def isProject (env : Environment) (idx : Std.HashSet Nat) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => idx.contains i
  | none   => false

/-- 沿项目内部声明做传递闭包。注意 `value? true`：定理的证明项只有带上这个参数才取得到，
默认的 `value?` 对 `thmInfo` 返回 `none`——那会让闭包在第一个定理处就断掉。 -/
private partial def expand (env : Environment) (pIdx : Std.HashSet Nat) (seen : NameSet)
    (order : Array Name) (todo : List Name) : NameSet × Array Name :=
  match todo with
  | [] => (seen, order)
  | n :: rest =>
    if seen.contains n then
      expand env pIdx seen order rest
    else
      let seen := seen.insert n
      let order := order.push n
      match env.find? n with
      | none => expand env pIdx seen order rest
      | some ci =>
        let used := ci.type.getUsedConstants
        let used := match ci.value? true with
          | some v => used ++ v.getUsedConstants
          | none   => used
        let next := used.toList.filter (fun m => isProject env pIdx m && !seen.contains m)
        expand env pIdx seen order (next ++ rest)

private def jsonStr (s : String) : String :=
  let s1 := s.replace "\\" "\\\\"
  let s2 := s1.replace "\"" "\\\""
  "\"" ++ s2 ++ "\""

elab "#writeFrontier" : command => do
  let env ← getEnv
  let pIdx := projectIndices env
  let mut objs : Array String := #[]
  for t in frontierTargets do
    match env.find? t with
    | none => objs := objs.push (jsonStr t.toString ++ ":null")
    | some _ =>
      let (_, order) := expand env pIdx ∅ #[] [t]
      let mut extSet : NameSet := ∅
      let mut extOrder : Array Name := #[]
      for n in order do
        match env.find? n with
        | none => pure ()
        | some ci =>
          let used := ci.type.getUsedConstants
          let used := match ci.value? true with
            | some v => used ++ v.getUsedConstants
            | none   => used
          for m in used do
            unless isProject env pIdx m do
              unless extSet.contains m do
                extSet := extSet.insert m
                extOrder := extOrder.push m
      let mut projList : Array String := #[]
      for n in order do projList := projList.push (jsonStr n.toString)
      let mut extList : Array String := #[]
      for n in extOrder do
        let k := match env.find? n with
          | some ci => kindOf ci
          | none    => "unknown"
        let m := match env.getModuleIdxFor? n with
          | some i => (env.header.modules[i]!).module.toString
          | none   => "<current>"
        extList := extList.push
          ("[" ++ jsonStr n.toString ++ "," ++ jsonStr k ++ "," ++ jsonStr m ++ "]")
      let obj := jsonStr t.toString ++ ":{\"project\":[" ++
        ",".intercalate projList.toList ++ "],\"external\":[" ++
        ",".intercalate extList.toList ++ "]}"
      objs := objs.push obj
  let doc := "{\"targets\":{" ++ ",".intercalate objs.toList ++ "}}"
  liftIO <| IO.FS.writeFile frontierOutputFile doc

#writeFrontier
