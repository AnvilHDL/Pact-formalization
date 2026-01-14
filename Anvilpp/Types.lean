import Mathlib.Data.Finset.Basic
import Anvilpp.Base

inductive MessageExch : Type where
  | send : MessageId → MessageExch
  | recv : MessageId → MessageExch

namespace MessageExch
  def messageId : MessageExch → MessageId
    | send msg => msg
    | recv msg => msg
end MessageExch

/-- Process type. -/
inductive ProcTy : Type where
  | message : MessageExch → ProcTy
  | cycle : ProcTy
  | skip : ProcTy
  | dollar : ProcId → ProcTy
  | choice : ProcTy → ProcTy → ProcTy
  | choice_fair : BranchId → ProcTy → ProcTy → ProcTy
  | par : ProcTy → ProcTy → ProcTy
  | seq : ProcTy → ProcTy → ProcTy
  | xoffer : ProcTy → List (MessageExch × ProcTy) → ProcTy
  | offer : ProcTy → List (MessageExch × ProcTy) → ProcTy
  | var : String → ProcTy
  | recur : String → ProcTy → ProcTy
