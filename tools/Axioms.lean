import Lean
import E0
import E1
import E2
import E2Nicea
import E3
import E3Nicea
import E4
import E5
import E6
import E7
import E8
import Ciclo
import CicloNicea
import CicloPaso
import CicloRetornos
import CicloRetornosB
import CicloF2
import CicloModelo
import CicloF4
import CicloF4b
import CicloF5a
import CicloF5
import CicloF6
import CicloCaso
import CicloEnlaces
import CicloDeclive
import CicloSub012

/-! Auditoría de axiomas: recorre todo `theorem` de los módulos del proyecto
    y cuenta los axiomas de los que depende. Uso: `lake env lean tools/Axioms.lean` -/
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : List Name := [`E0,`E1,`E2,`E2Nicea,`E3,`E3Nicea,`E4,`E5,`E6,`E7,`E8,`Ciclo,`CicloNicea,
    `CicloPaso,`CicloRetornos,`CicloRetornosB,`CicloF2,`CicloModelo,`CicloF4,`CicloF4b,`CicloF5a,
    `CicloF5,`CicloF6,`CicloCaso,`CicloEnlaces,`CicloDeclive,`CicloSub012]
  let mut total := 0
  let mut sorryCount := 0
  let mut seen : Array Name := #[]
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo _ =>
      match env.getModuleIdxFor? n with
      | some idx =>
        if mods.contains env.header.moduleNames[idx.toNat]! then
          total := total + 1
          let ax ← liftCoreM (collectAxioms n)
          if ax.contains ``sorryAx then sorryCount := sorryCount + 1
          for a in ax do
            unless seen.contains a do seen := seen.push a
      | none => pure ()
    | _ => pure ()
  logInfo m!"teoremas revisados: {total}\ncon sorryAx: {sorryCount}\naxiomas distintos: {seen.toList}"
