(**
  First attempt at a Gallina encoding of K-FOG-ish game formulas
  with player-tagged binders and an evaluator.
*)

Require Import Coq.Lists.List.
Import ListNotations.

Module KGame.

  (* ------------------------------------------------------------- *)
  (* 0. Parameters / placeholders                                  *)
  (* ------------------------------------------------------------- *)

  (* Number of players. You can make this a nat parameter. *)
  Parameter K : nat.

  (* We'll just take players as nats < K for now. *)
  Definition player := nat.

  (* A structure's domain. In your paper this is |M|. *)
  Parameter dom : Type.

  (* Variables: we’ll model them as strings or de Bruijns; keep abstract. *)
  Parameter var : Type.

  (* First-order formulas over your signature; abstract for now. *)
  Parameter formula : Type.

  (* An assignment maps vars to domain elements. *)
  Definition assignment := var -> dom.

  (* Update an assignment. *)
  Definition assign (s : assignment) (x : var) (a : dom) : assignment :=
    fun y => if (* some decidable equality on var *) admit (* var_eq x y *)
             then a else s y.

  (* Satisfaction relation for FO formulas in a structure.
     We're not building structures here; just assume a satisfaction oracle. *)
  Parameter satisfies : assignment -> formula -> bool.
  (* In the paper this is (M, s ⊨ φ); here we just get a bool. *)

  (* A K-tuple of booleans: simplest is a list of length K. *)
  Definition outcome := list bool.

  (* A well-formed outcome should have length K, but we'll just assert that. *)


  (* ------------------------------------------------------------- *)
  (* 1. Game syntax                                                 *)
  (* ------------------------------------------------------------- *)

  Inductive game : Type :=
  | GEnd  : (player -> formula) -> game
    (* terminal ⟨φ_0, …, φ_{K-1}⟩ *)
  | GBind : player -> var -> game -> game.
    (* P_i x. Φ *)

  (* This is exactly your
       P_{i1} x1. ... P_{in} xn. ⟨φ0,...,φ_{K-1}⟩
     structure. *)


  (* ------------------------------------------------------------- *)
  (* 2. Strategies and profiles                                     *)
  (* ------------------------------------------------------------- *)

  (**
    A pure strategy for player i:
    - we must know at which subgame we are (the paper has σ_i(Ψ, s))
    - we must know the current assignment
    and we must return a dom element.
   *)

  (* We’ll pass the *current* subgame explicitly. *)
  Definition strategy := game -> assignment -> dom.

  (* A strategy profile: one strategy per player. *)
  Definition profile := player -> strategy.


  (* ------------------------------------------------------------- *)
  (* 3. Evaluator                                                   *)
  (* ------------------------------------------------------------- *)

  Fixpoint eval (g : game) (σ : profile) (s : assignment) : outcome :=
    match g with
    | GEnd fos =>
        (* build the K-length outcome by querying fos 0..K-1 *)
        let fix build (i : nat) : outcome :=
            match i with
            | O => []
            | S i' =>
                (* players are 0 .. K-1; here we assume i' < K somehow *)
                let rest := build i' in
                let p   := K - S i' in  (* hacky way to go 0..K-1 in order *)
                (* better: just build in increasing order with an aux index *)
                rest
            end
        in
        (* ok, do it properly: *)
        let fix build_from (i : nat) : outcome :=
            match i with
            | O => []
            | S i' =>
                let tl := build_from i' in
                (* evaluate player (i'-th) formula *)
                let φ := fos i' in
                let b := satisfies s φ in
                tl ++ [b]
            end
        in build_from K

    | GBind i x g' =>
        (* ask player i's strategy, then continue *)
        let a := σ i g s in
        let s' := assign s x a in
        eval g' σ s'
    end.

  (* The messy bit above is just "evaluate each terminal formula in order".
     You can clean that up by using vectors (Coq.Vectors.Vector) instead of lists.
   *)


  (* ------------------------------------------------------------- *)
  (* 4. Notes on well-formedness                                    *)
  (* ------------------------------------------------------------- *)

  (**
    - We haven't enforced i < K; in real Coq code you’d either:
        * make player := { i : nat | i < K } (a finite type), or
        * use Fin.t K.
    - We haven't given equality on var, so assign is admitted.
    - We haven’t represented the structure �� explicitly; we hid it
      inside [satisfies].
    - But the *shape* is right:
        game syntax + single strategy per player + evaluator that
        reuses that strategy at every GBind for that player.
   *)

End KGame.
