Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import BasicUtility.
Require Import MathSpec.
Require Import Classical_Prop.
(**********************)
(** Unitary Programs **)
(**********************)

Declare Scope exp_scope.
Delimit Scope exp_scope with exp.
Local Open Scope exp_scope.
Local Open Scope nat_scope.

Open Scope ucom.

(* This file defines the syntax of Quantum Abstract Machine.*)
(**************** Data Type ********************** *
Var                        x,y

Quantum Channel            c,d
Classical Channel          a
Projective Channel         hat_c, hat_d
Quantum Related Channel    α := c | hat_c
All Channel                δ := α | a

Message Name               e
Quantum Message            q := unit | e | c.μ | hat_c.q | †q
Classical Message          ι := hat_q | a.ι | hat_c.ι | †ι 
All Message                μ := q | ι

Channels and Message       κ := μ | δ
************************************************** *)
(***      Data type    ***)
Definition var : Type := nat.

Definition q_ch : Type := nat.
Definition c_ch : Type := nat.
Inductive  proj_ch : Type := ProjC (c : q_ch).

Inductive qrel_ch := Qch (c : q_ch) | QPch (c : proj_ch).
Inductive all_ch := QRch (c : qrel_ch) | Cch (a: c_ch). 

Definition mess_n : Type := nat.
Inductive  q_mess := UNIT | Mess (e: mess_n) | ChMess (c: q_ch) (m: all_mess) | PjMess (pc: proj_ch) (q: q_mess) | DagQ (q: q_mess)
with       c_mess := HatQ (q: q_mess) | CChMess (a: c_ch) (i: c_mess) | DagC (i: c_mess)
with       all_mess := Qmess (q: q_mess) | Cmess (c: c_mess).

Inductive all_mess_ch := C (d: all_ch) | M (m: all_mess).

(******************* Syntax ************************ *
Resources         ϕ := c.μ | hat_c.μ | unit      
Action            A := νc | a!ι | δ?(x) | α◃κ | c▹(x)
Process           R,T := 0 | AR | R+T | !R
Raw Membrane      M,N := R | ϕ
Membrane          P,Q := {|Bar_M|} | R<ϕ|P | P[ϕ]Q
************************************************** *)
(***      Syntax     ***)
Inductive resource := ChMessR (c: q_ch) (m: all_mess) | PJMessR (pc: proj_ch) (m: all_mess) | U.

Inductive action := CreatC (c: q_ch) | CSend (a: c_ch) (i: c_mess) | Recv (d: all_ch) (x: var) | Encode (al: qrel_ch) (k: all_mess_ch) | Decode (c: q_ch) (x: var). 

Inductive process := Nil | AR (a: action) (r: process) | Choice (r: process) (t: process) | Rept (r: process).

Definition m_name := nat.
Inductive memb := Memb (m: m_name) (l : list process) (r: list resource).

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.


(* Defining program semantic functions. *)
Definition get_memb_info (menv: m_name -> nat) (m1: memb) (m2: memb) :=
  match m1, m2 with
  |(Memb mn1 _ _), (Memb mn2 _ _) => (menv mn1, menv mn2)
  end.


 (* return circuit *)
Fixpoint eval_process (p1: memb) (p2: memb) (idx: nat*nat) (n: nat) (b: bool): (memb * memb * bool * resource) * base_ucom (2*n) :=
  match p1, p2 with
  |(Memb mn1 _ _), (Memb mn2 _ _) => (((Memb mn1 [] []), (Memb mn2 [] []), b, U), H 0; H 1)
end.

(* Definition update_menv (m1: m_name) (m2: m_name) := m_name -> nat. *)
  
(* return circuit *)
Program Fixpoint eval_memb (menv: m_name -> nat) (update_menv: (m_name -> nat) -> (m_name-> nat)) (exp : memb * memb * bool * resource) (n: nat) : base_ucom (2*n) :=
  match exp with
  |((Memb _ [] _), (Memb _ [] _), _, _) =>  ID 0
  |((Memb mn1 (h::l) _) as m1, (Memb mn2 (h1::l1) _) as m2, _, _) =>
     (match eval_process m1 m2 (get_memb_info menv m1 m2) n true with
      |(exp', c) => c; (eval_memb (update_menv menv) update_menv exp' n)
      end )
  |((Memb mn1 []  _) as m1, (Memb mn2 (h1::l1) _) as m2, _, _) => ID 0
  |((Memb mn1 (h::l) _) as m1, (Memb mn2 []  _) as m2, _, _) => ID 0
  end.






















(* This is the semantics for basic gate set of the language. *)
Fixpoint exp_sem (env:var -> nat) (e:exp) (st: posi -> val) : (posi -> val) :=
   match e with (SKIP p) => st
              | X p => (st[p |-> (exchange (st p))])
              | CU p e' => if get_cua (st p) then exp_sem env e' st else st
              | RZ q p => (st[p |-> times_rotate (st p) q])
              | RRZ q p => (st[p |-> times_r_rotate (st p) q])
              | SR n x => sr_rotate st x n (*n is the highest position to rotate. *)
              | SRR n x => srr_rotate st x n
              | Lshift x => (lshift st x (env x))
              | Rshift x => (rshift st x (env x))
              | Rev x => (reverse st x (env x))
               | QFT x b => turn_qft st x b (env x)
               | RQFT x b => turn_rqft st x b (env x)
              | e1 ; e2 => exp_sem env e2 (exp_sem env e1 st)
    end.


Definition or_not_r (x y:var) (n1 n2:nat) := x <> y \/ n1 < n2.

Definition or_not_eq (x y:var) (n1 n2:nat) := x <> y \/ n1 <= n2.



Inductive exp_fresh (aenv:var->nat): posi -> exp -> Prop :=
      | skip_fresh : forall p p1, p <> p1 -> exp_fresh aenv p (SKIP p1)
      | x_fresh : forall p p' , p <> p' -> exp_fresh aenv p (X p')
      | sr_fresh : forall p x n, or_not_r (fst p) x n (snd p) -> exp_fresh aenv p (SR n x)
      | srr_fresh : forall p x n, or_not_r (fst p) x n (snd p) -> exp_fresh aenv p (SRR n x)
      | lshift_fresh : forall p x, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (Lshift x)
      | rshift_fresh : forall p x, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (Rshift x)
      | rev_fresh : forall p x, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (Rev x)
      | cu_fresh : forall p p' e, p <> p' -> exp_fresh aenv p e -> exp_fresh aenv p (CU p' e)
     (* | cnot_fresh : forall p p1 p2, p <> p1 -> p <> p2 -> exp_fresh aenv p (HCNOT p1 p2) *)
      | rz_fresh : forall p p' q, p <> p' -> exp_fresh aenv p (RZ q p')
      | rrz_fresh : forall p p' q, p <> p' -> exp_fresh aenv p (RRZ q p')
       (*all qubits will be touched in qft/rqft because of hadamard*)
      | qft_fresh : forall p x b, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (QFT x b)
      | rqft_fresh : forall p x b, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (RQFT x b)
      | seq_fresh : forall p e1 e2, exp_fresh aenv p e1 -> exp_fresh aenv p e2 -> exp_fresh aenv p (Seq e1 e2).

(* Defining matching shifting stack. *)
Inductive sexp := Ls | Rs | Re.

Definition opp_ls (s : sexp) := match s with Ls => Rs | Rs => Ls | Re => Re end.

Definition fst_not_opp (s:sexp) (l : list sexp) := 
   match l with [] => True
              | (a::al) => s <> opp_ls a
   end.

Inductive exp_neu_l (x:var) : list sexp -> exp ->  list sexp -> Prop :=
      | skip_neul : forall l p, exp_neu_l x l (SKIP p) l
      | x_neul : forall l p,  exp_neu_l x l (X p) l
      | sr_neul : forall l y n, exp_neu_l x l (SR n y) l
      | srr_neul : forall l y n, exp_neu_l x l (SRR n y) l
      | cu_neul : forall l p e, exp_neu_l x [] e [] -> exp_neu_l x l (CU p e) l
      (*| hcnot_neul : forall l p1 p2, exp_neu_l x l (HCNOT p1 p2) l *)
      | rz_neul : forall l p q, exp_neu_l x l (RZ q p) l
      | rrz_neul : forall l p q, exp_neu_l x l (RRZ q p) l
      | qft_neul : forall l y b, exp_neu_l x l (QFT y b) l
      | rqft_neul : forall l y b, exp_neu_l x l (RQFT y b) l

      | lshift_neul_a : forall l, exp_neu_l x (Rs::l) (Lshift x) l
      | lshift_neul_b : forall l, fst_not_opp Ls l -> exp_neu_l x l (Lshift x) (Ls::l)
      | lshift_neul_ne : forall l y, x <> y -> exp_neu_l x l (Lshift y) l
      | rshift_neul_a : forall l, exp_neu_l x (Ls::l) (Rshift x) l
      | rshift_neul_b : forall l, fst_not_opp Rs l -> exp_neu_l x l (Rshift x) (Rs::l)
      | rshift_neul_ne : forall l y, x <> y -> exp_neu_l x l (Rshift y) l
      | rev_neul_a : forall l, exp_neu_l x (Re::l) (Rev x) l
      | rev_neul_b : forall l, fst_not_opp Re l -> exp_neu_l x l (Rev x) (Re::l)
      | rev_neul_ne : forall l y, x <> y -> exp_neu_l x l (Rev y) l
      | seq_neul : forall l l' l'' e1 e2, exp_neu_l x l e1 l' -> exp_neu_l x l' e2 l'' -> exp_neu_l x l (Seq e1 e2) l''.

Definition exp_neu (xl : list var) (e:exp) : Prop :=
    forall x, In x xl -> exp_neu_l x [] e [].

Definition exp_neu_prop (l:list sexp) :=
    (forall i a, i + 1 < length l -> nth_error l i = Some a -> nth_error l (i+1) <> Some (opp_ls a)).

(* Type System. *)
Inductive well_typed_exp: env -> exp -> Prop :=
    | skip_refl : forall env, forall p, well_typed_exp env (SKIP p)
    | x_nor : forall env p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (X p)
    (*| x_had : forall env p, Env.MapsTo (fst p) Had env -> well_typed_exp env (X p) *)
    (*| cnot_had : forall env p1 p2, p1 <> p2 -> Env.MapsTo (fst p1) Had env -> Env.MapsTo (fst p2) Had env
                         -> well_typed_exp env (HCNOT p1 p2) *)
    | rz_nor : forall env q p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (RZ q p)
    | rrz_nor : forall env q p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (RRZ q p)
    | sr_phi : forall env b m x, Env.MapsTo x (Phi b) env -> m < b -> well_typed_exp env (SR m x)
    | srr_phi : forall env b m x, Env.MapsTo x (Phi b) env -> m < b -> well_typed_exp env (SRR m x)
    | lshift_nor : forall env x, Env.MapsTo x Nor env -> well_typed_exp env (Lshift x)
    | rshift_nor : forall env x, Env.MapsTo x Nor env -> well_typed_exp env (Rshift x)
    | rev_nor : forall env x, Env.MapsTo x Nor env -> well_typed_exp env (Rev x).

Fixpoint get_vars e : list var :=
    match e with SKIP p => [(fst p)]
              | X p => [(fst p)]
              | CU p e => (fst p)::(get_vars e)
             (* | HCNOT p1 p2 => ((fst p1)::(fst p2)::[]) *)
              | RZ q p => ((fst p)::[])
              | RRZ q p => ((fst p)::[])
              | SR n x => (x::[])
              | SRR n x => (x::[])
              | Lshift x => (x::[])
              | Rshift x => (x::[])
              | Rev x => (x::[])
              | QFT x b => (x::[])
              | RQFT x b => (x::[])
              | Seq e1 e2 => get_vars e1 ++ (get_vars e2)
   end.


Inductive well_typed_oexp (aenv: var -> nat) : env -> exp -> env -> Prop :=
    | exp_refl : forall env e, 
                well_typed_exp env e -> well_typed_oexp aenv env e env
    | qft_nor :  forall env env' x b, b <= aenv x -> 
               Env.MapsTo x Nor env -> Env.Equal env' (Env.add x (Phi b) env)
                   -> well_typed_oexp aenv env (QFT x b) env'
    | rqft_phi :  forall env env' x b, b <= aenv x ->
               Env.MapsTo x (Phi b) env -> Env.Equal env' (Env.add x Nor env) -> 
                 well_typed_oexp aenv env (RQFT x b) env'
    | pcu_nor : forall env p e, Env.MapsTo (fst p) Nor env -> exp_fresh aenv p e -> exp_neu (get_vars e) e ->
                       well_typed_oexp aenv env e env -> well_typed_oexp aenv env (CU p e) env
    | pe_seq : forall env env' env'' e1 e2, well_typed_oexp aenv env e1 env' -> 
                 well_typed_oexp aenv env' e2 env'' -> well_typed_oexp aenv env (e1 ; e2) env''.

Inductive exp_WF (aenv:var -> nat): exp -> Prop :=
      | skip_wf : forall p, snd p < aenv (fst p) -> exp_WF aenv (SKIP p)
      | x_wf : forall p, snd p < aenv (fst p)  -> exp_WF aenv  (X p)
      | cu_wf : forall p e, snd p < aenv (fst p)  -> exp_WF aenv  e -> exp_WF aenv  (CU p e)
    (*  | hcnot_wf : forall p1 p2, snd p1 < aenv (fst p1) 
                              -> snd p2 < aenv (fst p2)  -> exp_WF aenv  (HCNOT p1 p2) *)
      | rz_wf : forall p q, snd p < aenv (fst p)  -> exp_WF aenv  (RZ q p)
      | rrz_wf : forall p q, snd p < aenv (fst p)  -> exp_WF aenv  (RRZ q p)
      | sr_wf : forall n x, n < aenv x -> exp_WF aenv  (SR n x)
      | ssr_wf : forall n x, n < aenv x -> exp_WF aenv  (SRR n x)       
      | seq_wf : forall e1 e2, exp_WF aenv e1 -> exp_WF aenv  e2 -> exp_WF aenv  (Seq e1 e2)
      | lshift_wf : forall x, 0 < aenv x -> exp_WF aenv  (Lshift x)
      | rshift_wf : forall x, 0 < aenv x -> exp_WF aenv  (Rshift x)
      | rev_wf : forall x, 0 < aenv x -> exp_WF aenv  (Rev x)
      | qft_wf : forall x b, b <= aenv x -> 0 < aenv x -> exp_WF aenv (QFT x b)
      | rqft_wf : forall x b, b <= aenv x -> 0 < aenv x -> exp_WF aenv (RQFT x b).

Fixpoint init_v (n:nat) (x:var) (M: nat -> bool) :=
      match n with 0 => (SKIP (x,0))
                | S m => if M m then init_v m x M; X (x,m) else init_v m x M
      end.

Inductive right_mode_val : type -> val -> Prop :=
    | right_nor: forall b r, right_mode_val Nor (nval b r)

    | right_phi: forall n rc r, right_mode_val (Phi n) (qval rc r).

Definition right_mode_env (aenv: var -> nat) (env: env) (st: posi -> val)
            := forall t p, snd p < aenv (fst p) -> Env.MapsTo (fst p) t env -> right_mode_val t (st p).

(* helper functions/lemmas for NOR states. *)
Definition nor_mode (f : posi -> val)  (x:posi) : Prop :=
       match f x with nval a b => True | _ => False end.

Definition nor_modes (f:posi -> val) (x:var) (n:nat) :=
      forall i, i < n -> nor_mode f (x,i).

Definition get_snd_r (f:posi -> val) (p:posi) :=
    match (f p) with qval rc r => r | _ => allfalse end.

Definition qft_uniform (aenv: var -> nat) (tenv:env) (f:posi -> val) :=
   forall x b, Env.MapsTo x (Phi b) tenv -> 
             (forall i, i < b -> get_snd_r f (x,i) = (lshift_fun (get_r_qft f x) i)).

Definition qft_gt (aenv: var -> nat) (tenv:env) (f:posi -> val) :=
   forall x b, Env.MapsTo x (Phi b) tenv -> (forall i,0 < b <= i -> get_r_qft f x i = false)
                                      /\ (forall j, b <= j < aenv x -> (forall i, 0 < i -> get_snd_r f (x,j) i = false )).

Definition at_match (aenv: var -> nat) (tenv:env) := forall x b, Env.MapsTo x (Phi b) tenv -> b <= aenv x.
