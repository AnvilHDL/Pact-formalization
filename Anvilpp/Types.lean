import Mathlib.Data.Finset.Basic
import Anvilpp.Base

inductive MessageExch : Type where
  | send : MessageId → MessageExch
  | recv : MessageId → MessageExch

/-- Process type. -/
inductive ProcTy : Type where
  | message : MessageExch → ProcTy → ProcTy
  | cycle : ProcTy
  | dollar : ProcId → ProcTy
  | choice : ProcTy → ProcTy → ProcTy
  | choice_fair : BranchId → ProcTy → ProcTy → ProcTy
  | par : ProcTy → ProcTy → ProcTy
  | seq : ProcTy → ProcTy → ProcTy
  | xoffer : ProcTy → List (MessageExch × ProcTy) → ProcTy
  | offer : ProcTy → List (MessageExch × ProcTy) → ProcTy
  | var : String → ProcTy
  | recur : String → ProcTy → ProcTy
