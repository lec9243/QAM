Require Import PeanoNat Permut Setoid.
Require Import List.
Import ListNotations.
(**** Untilities ****)

(* This file defines the syntax of Quantum Abstract Machine.
Var               x,y
Message Name      e
Quantum Channel   c,d
Classical Channel h_c, h_d
Channel           delta := c | h_c
Quantum Message   q := unit | e | c.miu | dagger_q
Classical Message iota := h_q 
Message           miu := q | iota
Contexts          phi := list (c)d.miu      
Action            A := c_down | c_up | h_c!iota_send | delta?(x)_recv 
                      | c encode miu | c!(x)_decode | q!miu(x)_encode | q!(x)_decode
                      | c?(x)_trans 
Process           R,T := 0 | AR | R+T | !R
Raw Membrane      M,N := {|bar_R|}
Membrane          P,Q := {|Bar_R|}phi | R{|Bar_T|}phi | P[(c)d.miu]Q
*)
(*********************************************)
(***      Syntax     ***)
Definition var := nat.

Definition mess_n : Type := nat. (* message name *)
Definition chan_n : Type := nat. (* channel name *)

Definition qchan : Type := chan_n.
Definition cchan : Type := chan_n.
(* Inductive channel:= QC (q : qchan) | CC (c : cchan). *)
Inductive qmess := Unit | Mess (m : mess_n) | ChanM (c : chan_m) | PartM (q : qmess)
with      chan_m := ChM (c : qchan) (mu : mess)
with      cmess := MeasureQ (q : qmess)
with      mess   := QtM (q: qmess) | CcM (c: cmess).

Inductive shareC := ShareC (c : chan_n) (m : chan_m).

Definition contexts  := list shareC.

Inductive action := CreatC (c : qchan) | QSwap (c : qchan)
               | CSend (cc : cchan) (cm : cmess) | CRecv (cc : cchan) (x : var)
               | LEncode (q : qmess) (mu : mess) (x : var) | LDecode (q : qmess) (x : var)
               | GEncode (c : qchan) (x : mess_n) | GDecode (c : qchan) (x : var)
               | Trans (c : qchan) (x : var).

Inductive process := Nil | AR (a : action) (r : process) | Choice (p : process) (r : process) | Rept (r : process).

Definition rmemb := list process.

Inductive memb := CtxM (r : rmemb) (phi : contexts) | ALock (r : process) (t : memb) | ActM (p : memb) (c : shareC) (Q: memb).

Definition config := list memb.



(***      Semantics   ***)
(** Free Channel **)
Fixpoint FC_con (cx : contexts) :=
  match cx with
  | [] => []
  | ((ShareC c (ChM d m)) :: t) => c :: d :: (FC_con t)
  end.

Fixpoint FC_qmess (q : qmess) :=
  match q with
  | Unit | Mess _ => []
  | ChanM (ChM c mu) => c :: (FC_mess mu)
  | PartM q => FC_qmess q
  end
with FC_mess (mu : mess) :=
  match mu with
  | CcM _ => []
  | QtM q => FC_qmess q
  end.

Definition FC_action (a :action) :=
       match a with
       | CreatC c | QSwap c | GEncode c _ | GDecode c _ | Trans c _ => [c]
       | CSend _ _ | CRecv _ _ => []
       | LEncode q m _ => (FC_qmess q) ++ (FC_mess m)
       | LDecode q _ => FC_qmess q
 
end.

Fixpoint FC_process (r : process) :=
  match r with
  | Nil => []
  | AR a p =>  (FC_process p) ++ (FC_action a)
  | Choice p q => (FC_process p) ++ (FC_process q)
  | Rept p => FC_process p
  end.


(** Message Algebra **)
Fixpoint eq_qmess (q1 : qmess) (q2 : qmess) :=
  match q1, q2 with
  | Unit, Unit => true
  | Mess n1, Mess n2 => Nat.eqb n1 n2
  | ChanM (ChM c1 m1), ChanM (ChM c2 m2) => if Nat.eqb c1 c2 then eq_mess m1 m2 else false
  | PartM q1, PartM q2 => eq_qmess q1 q2
  | _ , _  => false
  end
with eq_cmess (c1 : cmess) (c2 : cmess) :=
       match c1, c2 with
       | MeasureQ q1, MeasureQ q2 => eq_qmess q1 q2
       end
with eq_mess (m1 : mess) (m2 : mess) :=
       match m1, m2 with
       | QtM q1, QtM q2 => eq_qmess q1 q2
       | CcM c1, CcM c2 => eq_cmess c1 c2
       | _, _ => false
      end.
                                                                      
Definition recover_mess m1 m2 :=
  match m1, m2 with
  | QtM q, QtM Unit => QtM q
  | QtM Unit, QtM q => QtM q
  | CcM (MeasureQ q1), QtM q2 => if eq_qmess q1 q2 then QtM q1 else QtM Unit 
  | QtM q1, CcM (MeasureQ q2) => if eq_qmess q1 q2 then QtM q1 else QtM Unit
  | _, _ => QtM Unit
  end.

(** Op Sem **)
Fixpoint replace_mess (p : process) (x: var) (m : mess) : process := p. (*TODO*)

Inductive process_sem : process -> rmemb -> Prop :=
| choose_l : forall p1 p2,  process_sem (Choice p1 p2) [p1]
| choose_r : forall p1 p2, process_sem (Choice p1 p2) [p2]
| mt : forall p1,  process_sem (Rept p1) [p1; p1]
| nt : forall p1,  process_sem (Rept p1) [Nil].


Inductive qam_sem : config -> config -> Prop :=
| mem_split : forall (p1 : process) (p2 : rmemb), qam_sem [(CtxM (p1 :: p2) [])] [(CtxM [p1] []); (CtxM p2 [])]
(* | cohere : forall
| decohere :
| encode :
| decode :
| assemble
| extract : *) 
| transfer : forall m c d x p mb1 mb2, qam_sem [(ActM (ALock (AR (Trans d x) p) mb1) (ShareC c (ChM d m)) mb2)]  [(ALock (replace_mess p x m) mb1); mb2] 
(*| commu
| swap*) .  

