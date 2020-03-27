open Fol
(*    
open Pp
open Prover
open Ctxt
*)

(* Misc tests *)
let p1 = Prop_and (Prop_all ("z", Prop_pred (("x", 2), [ Tm_bv 0; Tm_fv "y" ])),
		   Prop_ex ("w", Prop_pred (("x", 2), [Tm_fv "y"; Tm_bv 0])))


let zero = Tm_fun (("O", 0), [])
let succ x = Tm_fun (("S", 1), [x])
let natP = ("nat", 1)
let ax_0_is_nat = Prop_pred (natP, [zero])
let ax_1_S_is_nat = Prop_all ("n", Prop_imp (Prop_pred (natP, [Tm_bv 0]), 
					Prop_pred (natP, [succ (Tm_bv 0)])))

let goal = Prop_ex ("n", Prop_pred (natP, [succ (succ (Tm_bv 0))]))

let pA = Prop_pred (("A", 0), [])
let pB = Prop_pred (("B", 0), [])
let pC = Prop_pred (("C", 0), [])
let pAimpB = Prop_imp (pA, pB)
let pAandC = Prop_and (pA, pC)
let pBandC = Prop_and (pB, pC)
let g  = [((gensym_lab_hint "axAimpB"), pAimpB); ((gensym_lab_hint "axAndC"), pAandC)]

