module

public import KFOL.Owner.Basis.WinnerSet

/-! The five-variable exchange presentation. A finite equational calculation
first derives the unrestricted action-band law from exchange and the other
native equations. Soundness and the existing word-normalization completeness
then identify the resulting thirty-six-equation theory. -/

@[expose] public section
namespace KFOL.Owner.FiniteBasis.FiveVariables
universe u
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/- The record only organizes hypotheses in the equational calculation. Its
connection to the independent native theory is proved below. -/
private structure Assumptions {M : Type u} (f : M → M → M) (h : M → M → M → M) : Prop where
  R1 (r : M) : (f r r) = r
  R2 (r a : M) : (f (f r a) r) = (f a r)
  R3 (r a : M) : (f (f r a) a) = (f r a)
  R4 (r a b : M) : (f r (f (f r a) b)) = (f r (f a b))
  R5 (r a b : M) : (f (f (f r a) b) a) = (f (f r b) a)
  R6 (r a b : M) : (f r (f a b)) = (f a (f r b))
  h_sym (r a b : M) : (h r a b) = (h r b a)
  h_minor (r a : M) : (h r a a) = (f a r)
  h_root (r a b : M) : (f (h r a b) r) = (h r a b)
  h_expand (r a b u : M) : (h (f u r) a b) = (f (f u r) (h r a b))
  h_back (r a b u : M) : (h r (f u a) b) = (h r (f (f u r) a) b)
  h_reroot (r a b u : M) : (f (h a u b) r) = (f (f (h r u b) a) r)
  h_insert (r a b : M) : (h r a b) = (h r (f r a) b)
  project_join (r a u v : M) : (f (f (f u a) (f v a)) r) = (f (f (f (f u a) r) r) (f (f (f v a) r) r))
  reset_split (a u v : M) : (f u (f v a)) = (f (f u a) (f v a))
  root_preserve (r u v : M) : (f (f u (f v r)) r) = (f u (f v r))
  F_idem (r a b u : M) : (h r (f (h r (f (f u r) a) b) a) b) = (h r (f (f u r) a) b)
  F_cb (r a b : M) : (h r (f (f b r) a) b) = (h r (f r a) b)
  terminal (r a b : M) : (h r (h r a b) b) = (h r (f a r) b)
  terminal_bound (r a b : M) : (f (f (h r a b) r) (f (f (f (f a r) r) (f (f b r) r)) r)) = (f (f (f a r) r) (f (f b r) r))
  terminal_weak (r a b : M) : (f (f (h r a b) r) (f (h r (f a r) b) r)) = (h r (f a r) b)
  exchange (r u a b c : M) : h r (h r (f u a) b) c = h r c (h r (h a u c) b)
variable {M : Type u} {f : M → M → M} {h : M → M → M → M}
private theorem guarded_reset_project (L : Assumptions f h) (a b c d : M) :
    (h a (f (f b a) c) d) = (h a (f b c) d) :=
  ((L.h_back a c d b)).symm

private theorem guarded_insert_root (L : Assumptions f h) (a b c : M) :
    (h a (f a b) c) = (h a b c) :=
  ((L.h_insert a b c)).symm

private theorem reset_common_projection (L : Assumptions f h) (a b c d : M) :
    (f (f (f a b) (f c b)) d) = (f (f (f a b) d) (f (f c b) d)) := by
  calc
    _ = (f (f (f (f a b) d) d) (f (f (f c b) d) d)) := (L.project_join d b a c)
    _ = (f (f (f a b) d) (f (f (f c b) d) d)) := (congrArg (fun q => (f q (f (f (f c b) d) d))) (L.R3 (f a b) d))
    _ = (f (f (f a b) d) (f (f c b) d)) := (congrArg (fun q => (f (f (f a b) d) q)) (L.R3 (f c b) d))


private theorem reset_same_root_join (L : Assumptions f h) (a b c : M) :
    (f (f a b) (f c b)) = (f a (f c b)) :=
  ((L.reset_split b a c)).symm

private theorem action_idempotent (L : Assumptions f h) (a b c d : M) :
    (h a b (f (h a (f c d) b) d)) = (h a (f c d) b) := by
  calc
    _ = (h a (f (h a (f c d) b) d) b) := ((L.h_sym a (f (h a (f c d) b) d) b)).symm
    _ = (h a (f (h a (f (f c a) d) b) d) b) := ((congrArg (fun q => (h a (f q d) b)) (guarded_reset_project L a c d b))).symm
    _ = (h a (f (f c a) d) b) := (L.F_idem a d b c)
    _ = (h a (f c d) b) := (guarded_reset_project L a c d b)


private theorem guarded_source_project (L : Assumptions f h) (a b c : M) :
    (h a b (f (f b a) c)) = (h a c b) := by
  calc
    _ = (h a (f (f b a) c) b) := ((L.h_sym a (f (f b a) c) b)).symm
    _ = (h a (f a c) b) := (L.F_cb a c b)
    _ = (h a c b) := (guarded_insert_root L a c b)


private theorem guarded_terminal (L : Assumptions f h) (a b c : M) :
    (h a (f b a) c) = (h a c (h a b c)) := by
  calc
    _ = (h a (h a b c) c) := ((L.terminal a b c)).symm
    _ = (h a c (h a b c)) := (L.h_sym a (h a b c) c)


private theorem reset_absorb_guarded (L : Assumptions f h) (a b c : M) :
    (f a (f b (h c a b))) = (f a (f b c)) := by
  calc
    _ = (f a (f b (f (h c a b) c))) := ((congrArg (fun q => (f a (f b q))) (L.h_root c a b))).symm
    _ = (f a (f (h c a b) (f b c))) := ((congrArg (fun q => (f a q)) (L.R6 (h c a b) b c))).symm
    _ = (f (h c a b) (f a (f b c))) := ((L.R6 (h c a b) a (f b c))).symm
    _ = (f (h c a b) (f (f a (f b c)) c)) := ((congrArg (fun q => (f (h c a b) q)) (L.root_preserve c a b))).symm
    _ = (f (h c a b) (f (f (f a c) (f b c)) c)) := ((congrArg (fun q => (f (h c a b) (f q c))) (reset_same_root_join L a c b))).symm
    _ = (f (h c a b) (f (f (f a c) (f (f b c) c)) c)) := ((congrArg (fun q => (f (h c a b) (f (f (f a c) q) c))) (L.R3 b c))).symm
    _ = (f (h c a b) (f (f (f (f a c) c) (f (f b c) c)) c)) := ((congrArg (fun q => (f (h c a b) (f (f q (f (f b c) c)) c))) (L.R3 a c))).symm
    _ = (f (f (h c a b) c) (f (f (f (f a c) c) (f (f b c) c)) c)) := ((congrArg (fun q => (f q (f (f (f (f a c) c) (f (f b c) c)) c))) (L.h_root c a b))).symm
    _ = (f (f (f a c) c) (f (f b c) c)) := (L.terminal_bound c a b)
    _ = (f (f a c) (f (f b c) c)) := (congrArg (fun q => (f q (f (f b c) c))) (L.R3 a c))
    _ = (f (f a c) (f b c)) := (congrArg (fun q => (f (f a c) q)) (L.R3 b c))
    _ = (f a (f b c)) := (reset_same_root_join L a c b)


private theorem guarded_weak_bound (L : Assumptions f h) (a b c : M) :
    (f (h a b c) (h a (f b a) c)) = (h a (f b a) c) := by
  calc
    _ = (f (h a b c) (f (h a (f b a) c) a)) := ((congrArg (fun q => (f (h a b c) q)) (L.h_root a (f b a) c))).symm
    _ = (f (f (h a b c) a) (f (h a (f b a) c) a)) := ((congrArg (fun q => (f q (f (h a (f b a) c) a))) (L.h_root a b c))).symm
    _ = (h a (f b a) c) := (L.terminal_weak a b c)


private theorem reset_distribute_projection (L : Assumptions f h) (a b c d : M) :
    (f (f a (f b c)) d) = (f (f a c) (f (f b c) d)) := by
  calc
    _ = (f (f (f a c) (f b c)) d) := ((congrArg (fun q => (f q d)) (reset_same_root_join L a c b))).symm
    _ = (f (f (f a c) d) (f (f b c) d)) := (reset_common_projection L a c b d)
    _ = (f (f a c) (f (f b c) d)) := (reset_same_root_join L (f a c) d (f b c))


private theorem reset_left_idempotent (L : Assumptions f h) (a b : M) :
    (f a (f a b)) = (f a b) := by
  calc
    _ = (f a (f (f a b) b)) := ((congrArg (fun q => (f a q)) (L.R3 a b))).symm
    _ = (f a (f b b)) := (L.R4 a b b)
    _ = (f a b) := (congrArg (fun q => (f a q)) (L.R1 b))


private theorem reset_guarded_root (L : Assumptions f h) (a b c d : M) :
    (f (f a b) (h b c d)) = (f a (h b c d)) := by
  calc
    _ = (h (f a b) c d) := ((L.h_expand b c d a)).symm
    _ = (f (h (f a b) c d) (f a b)) := ((L.h_root (f a b) c d)).symm
    _ = (f a (f (h (f a b) c d) b)) := (L.R6 (h (f a b) c d) a b)
    _ = (f a (f (f (f a b) (h b c d)) b)) := (congrArg (fun q => (f a (f q b))) (L.h_expand b c d a))
    _ = (f a (f (f a (h b c d)) b)) := (congrArg (fun q => (f a q)) (L.R5 a b (h b c d)))
    _ = (f a (f (h b c d) b)) := (L.R4 a (h b c d) b)
    _ = (f a (h b c d)) := (congrArg (fun q => (f a q)) (L.h_root b c d))


private theorem guarded_reset_root (L : Assumptions f h) (a b c d : M) :
    (h (f a b) c d) = (f a (h b c d)) := by
  calc
    _ = (f (f a b) (h b c d)) := (L.h_expand b c d a)
    _ = (f a (h b c d)) := (reset_guarded_root L a b c d)


private theorem guarded_reset_symm_project (L : Assumptions f h) (a b c d : M) :
    (h a (f b c) d) = (h a d (f (f b a) c)) := by
  calc
    _ = (h a (f (f b a) c) d) := ((guarded_reset_project L a b c d)).symm
    _ = (h a d (f (f b a) c)) := (L.h_sym a (f (f b a) c) d)


private theorem guarded_reroot_symm (L : Assumptions f h) (a b c d : M) :
    (f (h a b c) d) = (f (f (h d c b) a) d) := by
  calc
    _ = (f (h a c b) d) := ((congrArg (fun q => (f q d)) (L.h_sym a c b))).symm
    _ = (f (f (h d c b) a) d) := (L.h_reroot d a b c)


private theorem guarded_insert_right (L : Assumptions f h) (a b c : M) :
    (h a b (f a c)) = (h a c b) := by
  calc
    _ = (h a (f a c) b) := ((L.h_sym a (f a c) b)).symm
    _ = (h a c b) := (guarded_insert_root L a c b)


private theorem guarded_root_repeat (L : Assumptions f h) (a b : M) :
    (h a b a) = (h a a (f a b)) := by
  calc
    _ = (h a a (f (f a a) b)) := ((guarded_source_project L a a b)).symm
    _ = (h a a (f a b)) := (congrArg (fun q => (h a a (f q b))) (L.R1 a))


private theorem guarded_source_root (L : Assumptions f h) (a b : M) :
    (h a b (f b a)) = (h a a b) := by
  calc
    _ = (h a b (f (f b a) a)) := ((congrArg (fun q => (h a b q)) (L.R3 b a))).symm
    _ = (h a a b) := (guarded_source_project L a b a)


private theorem guarded_source_projection (L : Assumptions f h) (a b c : M) :
    (h a b (f (f b a) c)) = (h a b c) := by
  calc
    _ = (h a c b) := (guarded_source_project L a b c)
    _ = (h a b c) := (L.h_sym a c b)


private theorem guarded_nested_terminal (L : Assumptions f h) (a b c : M) :
    (h a b (h a c b)) = (h a b (f c a)) := by
  calc
    _ = (h a (f c a) b) := ((guarded_terminal L a c b)).symm
    _ = (h a b (f c a)) := (L.h_sym a (f c a) b)


private theorem reset_guarded_self (L : Assumptions f h) (a b : M) :
    (f a (h b a (f a b))) = (f a b) := by
  calc
    _ = (f a (f a (h b a (f a b)))) := ((reset_left_idempotent L a (h b a (f a b)))).symm
    _ = (f a (f (f a b) (h b a (f a b)))) := ((congrArg (fun q => (f a q)) (reset_guarded_root L a b a (f a b)))).symm
    _ = (f (f a b) (f a (h b a (f a b)))) := ((L.R6 (f a b) a (h b a (f a b)))).symm
    _ = (f (f a b) (f a (h b (f a b) a))) := ((congrArg (fun q => (f (f a b) (f a q))) (L.h_sym b (f a b) a))).symm
    _ = (f (f a b) (f a b)) := (reset_absorb_guarded L (f a b) a b)
    _ = (f a b) := (L.R1 (f a b))


private theorem guarded_project_split (L : Assumptions f h) (a b c : M) :
    (h a (f b a) c) = (f (h a b c) (h a c (f b a))) := by
  calc
    _ = (f (h a b c) (h a (f b a) c)) := ((guarded_weak_bound L a b c)).symm
    _ = (f (h a b c) (h a c (f b a))) := (congrArg (fun q => (f (h a b c) q)) (L.h_sym a (f b a) c))


private theorem guarded_project_repeat (L : Assumptions f h) (a b : M) :
    (h a b (f b a)) = (f b a) := by
  calc
    _ = (h a (f b a) b) := ((L.h_sym a (f b a) b)).symm
    _ = (f (h a b b) (h a (f b a) b)) := ((guarded_weak_bound L a b b)).symm
    _ = (f (f b a) (h a (f b a) b)) := (congrArg (fun q => (f q (h a (f b a) b))) (L.h_minor a b))
    _ = (f (f b a) (h a b (f b a))) := (congrArg (fun q => (f (f b a) q)) (L.h_sym a (f b a) b))
    _ = (f b (h a b (f b a))) := (reset_guarded_root L b a b (f b a))
    _ = (f b a) := (reset_guarded_self L b a)


private theorem guarded_root_minor (L : Assumptions f h) (a b : M) :
    (h a a b) = (f b a) := by
  calc
    _ = (h a b (f b a)) := ((guarded_source_root L a b)).symm
    _ = (f b a) := (guarded_project_repeat L a b)


private theorem guarded_root_minor_right (L : Assumptions f h) (a b : M) :
    (h a b a) = (f b a) := by
  calc
    _ = (h a a (f a b)) := (guarded_root_repeat L a b)
    _ = (f (f a b) a) := (guarded_root_minor L a (f a b))
    _ = (f b a) := (L.R2 a b)


private theorem exchange_rearrange (L : Assumptions f h) (a b c d e : M) :
    (h a b (h a (h c d b) e)) = (h a b (h a (f d c) e)) := by
  calc
    _ = (h a (h a (f d c) e) b) := ((L.exchange a d c e b)).symm
    _ = (h a b (h a (f d c) e)) := (L.h_sym a (h a (f d c) e) b)


private theorem reset_guarded_distribute (L : Assumptions f h) (a b c d e : M) :
    (f (f a (h b c d)) e) = (f (f a b) (f (h b c d) e)) := by
  calc
    _ = (f (f a (f (h b c d) b)) e) := ((congrArg (fun q => (f (f a q) e)) (L.h_root b c d))).symm
    _ = (f (f a b) (f (f (h b c d) b) e)) := (reset_distribute_projection L a (h b c d) b e)
    _ = (f (f a b) (f (h b c d) e)) := (congrArg (fun q => (f (f a b) (f q e))) (L.h_root b c d))


private theorem guarded_reset_companion (L : Assumptions f h) (a b c : M) :
    (f (h a b c) c) = (f (f b a) c) := by
  calc
    _ = (f (f (h c b c) a) c) := (L.h_reroot c a c b)
    _ = (f (f (f b c) a) c) := (congrArg (fun q => (f (f q a) c)) (guarded_root_minor_right L c b))
    _ = (f (f b a) c) := (L.R5 b c a)


private theorem guarded_insert_right_eq (L : Assumptions f h) (a b c : M) :
    (h a b (f a c)) = (h a b c) := by
  calc
    _ = (h a c b) := (guarded_insert_right L a b c)
    _ = (h a b c) := (L.h_sym a c b)


private theorem reset_guarded_companion_aux (L : Assumptions f h) (a b c : M) :
    (f (f (f a b) c) (h b a c)) = (f c (h b a c)) := by
  calc
    _ = (f (f (h b a c) c) (h b a c)) := ((congrArg (fun q => (f q (h b a c))) (guarded_reset_companion L b a c))).symm
    _ = (f c (h b a c)) := (L.R2 (h b a c) c)


private theorem reset_guarded_remove_prefix (L : Assumptions f h) (a b c d e : M) :
    (f (f (f a b) c) (h b d e)) = (f (f a c) (h b d e)) := by
  calc
    _ = (h (f (f (f a b) c) b) d e) := ((guarded_reset_root L (f (f a b) c) b d e)).symm
    _ = (h (f (f a c) b) d e) := (congrArg (fun q => (h q d e)) (L.R5 a b c))
    _ = (f (f a c) (h b d e)) := (guarded_reset_root L (f a c) b d e)


private theorem reset_guarded_symm (L : Assumptions f h) (a b c d : M) :
    (f a (h b c d)) = (f a (h b d c)) := by
  calc
    _ = (h (f a b) c d) := ((guarded_reset_root L a b c d)).symm
    _ = (h (f a b) d c) := (L.h_sym (f a b) c d)
    _ = (f a (h b d c)) := (guarded_reset_root L a b d c)


private theorem reset_guarded_drop_project (L : Assumptions f h) (a b c d e : M) :
    (f (f a b) (f c (h b d e))) = (f a (f c (h b d e))) := by
  calc
    _ = (f (f a b) (h (f c b) d e)) := ((congrArg (fun q => (f (f a b) q)) (guarded_reset_root L c b d e))).symm
    _ = (h (f (f a b) (f c b)) d e) := ((guarded_reset_root L (f a b) (f c b) d e)).symm
    _ = (h (f a (f c b)) d e) := (congrArg (fun q => (h q d e)) (reset_same_root_join L a b c))
    _ = (f a (h (f c b) d e)) := (guarded_reset_root L a (f c b) d e)
    _ = (f a (f c (h b d e))) := (congrArg (fun q => (f a q)) (guarded_reset_root L c b d e))


private theorem reset_guarded_insert (L : Assumptions f h) (a b c d : M) :
    (f a (h b c (f (f a b) d))) = (f a (h b c d)) := by
  calc
    _ = (h (f a b) c (f (f a b) d)) := ((guarded_reset_root L a b c (f (f a b) d))).symm
    _ = (h (f a b) c d) := (guarded_insert_right_eq L (f a b) c d)
    _ = (f a (h b c d)) := (guarded_reset_root L a b c d)


private theorem reset_guarded_companion (L : Assumptions f h) (a b c : M) :
    (f (f a b) (h c a b)) = (f b (h c a b)) := by
  calc
    _ = (f (f (f a c) b) (h c a b)) := ((reset_guarded_remove_prefix L a c b a b)).symm
    _ = (f b (h c a b)) := (reset_guarded_companion_aux L a c b)


private theorem guarded_nested_symm (L : Assumptions f h) (a b c d e : M) :
    (h a (h b c d) e) = (h a (h b d c) e) := by
  calc
    _ = (h a (f a (h b c d)) e) := ((guarded_insert_root L a (h b c d) e)).symm
    _ = (h a (f a (h b d c)) e) := ((congrArg (fun q => (h a q e)) (reset_guarded_symm L a b d c))).symm
    _ = (h a (h b d c) e) := (guarded_insert_root L a (h b d c) e)


private theorem reset_guarded_nested (L : Assumptions f h) (a b c : M) :
    (f a (f (h b c a) (h b a (f c b)))) = (f a (h b c a)) := by
  calc
    _ = (f a (f (h b c a) (h b a (h b c a)))) := ((congrArg (fun q => (f a (f (h b c a) q))) (guarded_nested_terminal L b a c))).symm
    _ = (f a (f (h b c a) b)) := (reset_absorb_guarded L a (h b c a) b)
    _ = (f a (h b c a)) := (congrArg (fun q => (f a q)) (L.h_root b c a))


private theorem guarded_project_right (L : Assumptions f h) (a b c d : M) :
    (h a b (f (f c a) d)) = (h a b (f c d)) := by
  calc
    _ = (h a (f c d) b) := ((guarded_reset_symm_project L a c d b)).symm
    _ = (h a b (f c d)) := (L.h_sym a (f c d) b)


private theorem guarded_source_reset (L : Assumptions f h) (a b c : M) :
    (h a b (f b c)) = (h a b c) := by
  calc
    _ = (h a (f b c) b) := ((L.h_sym a (f b c) b)).symm
    _ = (h a b (f (f b a) c)) := (guarded_reset_symm_project L a b c b)
    _ = (h a b c) := (guarded_source_projection L a b c)


private theorem reset_guarded_absorb (L : Assumptions f h) (a b c d : M) :
    (f a (h b c (f a d))) = (f a (h b c d)) := by
  calc
    _ = (f a (h b c (f (f a b) d))) := ((congrArg (fun q => (f a q)) (guarded_project_right L b c a d))).symm
    _ = (f a (h b c d)) := (reset_guarded_insert L a b c d)


private theorem guarded_transport_project (L : Assumptions f h) (a b c d : M) :
    (h a (f b c) d) = (h a d (h c d (f b c))) := by
  calc
    _ = (h a d (f (h a (f b c) d) c)) := ((action_idempotent L a d b c)).symm
    _ = (h a d (f (f (h c d (f b c)) a) c)) := (congrArg (fun q => (h a d q)) (guarded_reroot_symm L a (f b c) d c))
    _ = (h a d (f (h c d (f b c)) c)) := (guarded_project_right L a d (h c d (f b c)) c)
    _ = (h a d (h c d (f b c))) := (congrArg (fun q => (h a d q)) (L.h_root c d (f b c)))


private theorem guarded_project_split_eq (L : Assumptions f h) (a b c : M) :
    (f (h a b c) (h a c (f b a))) = (f c (h a b c)) := by
  calc
    _ = (f (h a b c) (h a c (h a b c))) := ((congrArg (fun q => (f (h a b c) q)) (guarded_nested_terminal L a c b))).symm
    _ = (f (f c (h a b c)) (h a c (h a b c))) := ((reset_guarded_companion L c (h a b c) a)).symm
    _ = (f (f c (h a b c)) (h a c (f b a))) := (congrArg (fun q => (f (f c (h a b c)) q)) (guarded_nested_terminal L a c b))
    _ = (f (f c a) (f (h a b c) (h a c (f b a)))) := (reset_guarded_distribute L c a b c (h a c (f b a)))
    _ = (f c (f (h a b c) (h a c (f b a)))) := (reset_guarded_drop_project L c a (h a b c) c (f b a))
    _ = (f c (h a b c)) := (reset_guarded_nested L c a b)


private theorem guarded_project (L : Assumptions f h) (a b c : M) :
    (h a (f b a) c) = (f c (h a b c)) := by
  calc
    _ = (f (h a b c) (h a c (f b a))) := (guarded_project_split L a b c)
    _ = (f c (h a b c)) := (guarded_project_split_eq L a b c)


private theorem guarded_project_symm (L : Assumptions f h) (a b c : M) :
    (h a b (f c a)) = (f b (h a c b)) := by
  calc
    _ = (h a (f c a) b) := ((L.h_sym a (f c a) b)).symm
    _ = (f b (h a c b)) := (guarded_project L a c b)


private theorem guarded_project_right_eq (L : Assumptions f h) (a b c : M) :
    (h a b (f c a)) = (f b (h a b c)) := by
  calc
    _ = (f b (h a c b)) := (guarded_project_symm L a b c)
    _ = (f b (h a b c)) := (congrArg (fun q => (f b q)) (L.h_sym a c b))


private theorem guarded_transport (L : Assumptions f h) (a b c d : M) :
    (h a (f b c) d) = (h a d (h c d b)) := by
  calc
    _ = (h a d (h c d (f b c))) := (guarded_transport_project L a b c d)
    _ = (h a d (f d (h c d b))) := (congrArg (fun q => (h a d q)) (guarded_project_right_eq L c d b))
    _ = (h a d (h c d b)) := (guarded_source_reset L a d (h c d b))


private theorem guarded_nested_collapse (L : Assumptions f h) (a b c d : M) :
    (h a b (h c b d)) = (h a b (f d c)) := by
  calc
    _ = (h a (f d c) b) := ((guarded_transport L a d c b)).symm
    _ = (h a b (f d c)) := (L.h_sym a (f d c) b)


private theorem guarded_swap_nested (L : Assumptions f h) (a b c d e : M) :
    (h a (h b c d) e) = (h a e (h b d c)) := by
  calc
    _ = (h a (h b d c) e) := ((guarded_nested_symm L a b d c e)).symm
    _ = (h a e (h b d c)) := (L.h_sym a (h b d c) e)


private theorem guarded_nested_reroot (L : Assumptions f h) (a b c d e : M) :
    (h a b (h c d e)) = (h a b (f (h a d e) c)) := by
  calc
    _ = (h a b (f (h c d e) c)) := ((congrArg (fun q => (h a b q)) (L.h_root c d e))).symm
    _ = (h a b (f (f (h c d e) a) c)) := ((guarded_project_right L a b (h c d e) c)).symm
    _ = (h a b (f (h a d e) c)) := (congrArg (fun q => (h a b q)) ((L.h_reroot c a e d)).symm)


private theorem guarded_nested_absorb (L : Assumptions f h) (a b c d e : M) :
    (h a b (h c d (f b e))) = (h a b (h c d e)) := by
  calc
    _ = (h a b (f b (h c d (f b e)))) := ((guarded_source_reset L a b (h c d (f b e)))).symm
    _ = (h a b (f b (h c d e))) := (congrArg (fun q => (h a b q)) (reset_guarded_absorb L b c d e))
    _ = (h a b (h c d e)) := (guarded_source_reset L a b (h c d e))


private theorem exchange_under_root (L : Assumptions f h) (a b c d e x : M) :
    (h a b (h c (h d e b) x)) = (h a b (h c (f e d) x)) := by
  calc
    _ = (h a b (f (h c (h d e b) x) c)) := ((congrArg (fun q => (h a b q)) (L.h_root c (h d e b) x))).symm
    _ = (h a b (h c b (h c (h d e b) x))) := ((guarded_nested_collapse L a b c (h c (h d e b) x))).symm
    _ = (h a b (h c b (h c (f e d) x))) := (congrArg (fun q => (h a b q)) (exchange_rearrange L c b d e x))
    _ = (h a b (f (h c (f e d) x) c)) := (guarded_nested_collapse L a b c (h c (f e d) x))
    _ = (h a b (h c (f e d) x)) := (congrArg (fun q => (h a b q)) (L.h_root c (f e d) x))


private theorem exchange_across_root (L : Assumptions f h) (a b c d e x : M) :
    (h a b (h c (f d e) x)) = (h a b (h c x (h e b d))) := by
  calc
    _ = (h a b (h c (h e d b) x)) := ((exchange_under_root L a b c e d x)).symm
    _ = (h a b (h c x (h e b d))) := (congrArg (fun q => (h a b q)) (guarded_swap_nested L c e d b x))


private theorem guarded_nested_exchange (L : Assumptions f h) (a b c d e x : M) :
    (h a b (h c d (h e b x))) = (h a b (h c d (f x e))) := by
  calc
    _ = (h a b (h c (f x e) d)) := ((exchange_across_root L a b c x e d)).symm
    _ = (h a b (h c d (f x e))) := (congrArg (fun q => (h a b q)) (L.h_sym c (f x e) d))


private theorem band_exchange (L : Assumptions f h) (r a b c d u : M) :
    (h r b (h a d (h c b (f u r)))) = (h r b (h a d (f (f u r) c))) :=
  (guarded_nested_exchange L r b a d c (f u r))

private theorem band_reroot (L : Assumptions f h) (r a b c d u : M) :
    (h r b (h a d (f (h a b (f u r)) c))) = (h r b (h a d (f (f u r) c))) := by
  calc
    _ = (h r b (h a d (f (f (h c b (f u r)) a) c))) := (congrArg (fun q => (h r b (h a d q))) (L.h_reroot c a (f u r) b))
    _ = (h r b (h a d (f (h c b (f u r)) c))) := (congrArg (fun q => (h r b q)) (guarded_project_right L a d (h c b (f u r)) c))
    _ = (h r b (h a d (h c b (f u r)))) := (congrArg (fun q => (h r b (h a d q))) (L.h_root c b (f u r)))
    _ = (h r b (h a d (f (f u r) c))) := (band_exchange L r a b c d u)


private theorem band_projection (L : Assumptions f h) (r a b c d u : M) :
    (h r b (h a d (h c b (f (f u r) a)))) = (h r b (h a d (f (f u r) c))) := by
  calc
    _ = (h r b (h a d (f (h a b (f (f u r) a)) c))) := (congrArg (fun q => (h r b q)) (guarded_nested_reroot L a d c b (f (f u r) a)))
    _ = (h r b (h a d (f (f b (h a b (f u r))) c))) := (congrArg (fun q => (h r b (h a d (f q c)))) (guarded_project_right_eq L a b (f u r)))
    _ = (h r b (h a d (f (f b a) (f (h a b (f u r)) c)))) := (congrArg (fun q => (h r b (h a d q))) (reset_guarded_distribute L b a b (f u r) c))
    _ = (h r b (h a d (f b (f (h a b (f u r)) c)))) := (congrArg (fun q => (h r b q)) (guarded_project_right L a d b (f (h a b (f u r)) c)))
    _ = (h r b (h a d (f (h a b (f u r)) c))) := (guarded_nested_absorb L r b a d (f (h a b (f u r)) c))
    _ = (h r b (h a d (f (f u r) c))) := (band_reroot L r a b c d u)


private theorem band_inner_root (L : Assumptions f h) (r a b c d u : M) :
    (h r b (f (h r d (h c b (f (f u r) a))) a)) = (h r b (h a d (f (f u r) c))) := by
  calc
    _ = (h r b (f (f (h a d (h c b (f (f u r) a))) r) a)) := (congrArg (fun q => (h r b q)) (L.h_reroot a r (h c b (f (f u r) a)) d))
    _ = (h r b (f (h a d (h c b (f (f u r) a))) a)) := (guarded_project_right L r b (h a d (h c b (f (f u r) a))) a)
    _ = (h r b (h a d (h c b (f (f u r) a)))) := (congrArg (fun q => (h r b q)) (L.h_root a d (h c b (f (f u r) a))))
    _ = (h r b (h a d (f (f u r) c))) := (band_projection L r a b c d u)


private theorem band_outer_root (L : Assumptions f h) (r a b c d u : M) :
    (h r b (f (h r d (f (f (h c b (f (f u r) a)) r) c)) a)) = (h r b (f (f (h a d (f (f u r) c)) r) a)) := by
  calc
    _ = (h r b (f (h r (f (h c b (f (f u r) a)) c) d) a)) := (congrArg (fun q => (h r b (f q a))) ((guarded_reset_symm_project L r (h c b (f (f u r) a)) c d)).symm)
    _ = (h r b (f (h r (h c b (f (f u r) a)) d) a)) := (congrArg (fun q => (h r b (f (h r q d) a))) (L.h_root c b (f (f u r) a)))
    _ = (h r b (f (h r d (h c b (f (f u r) a))) a)) := (congrArg (fun q => (h r b (f q a))) (L.h_sym r (h c b (f (f u r) a)) d))
    _ = (h r b (h a d (f (f u r) c))) := (band_inner_root L r a b c d u)
    _ = (h r b (f (h a d (f (f u r) c)) a)) := ((congrArg (fun q => (h r b q)) (L.h_root a d (f (f u r) c)))).symm
    _ = (h r b (f (f (h a d (f (f u r) c)) r) a)) := ((guarded_project_right L r b (h a d (f (f u r) c)) a)).symm


private theorem band_source_root (L : Assumptions f h) (r a b c d u : M) :
    (h r b (f (h r d (f (f (h c b (f (f u r) a)) r) c)) a)) = (h r b (f (h r d (f (f u r) c)) a)) := by
  calc
    _ = (h r b (f (f (h a d (f (f u r) c)) r) a)) := (band_outer_root L r a b c d u)
    _ = (h r b (f (h r d (f (f u r) c)) a)) := ((congrArg (fun q => (h r b q)) (L.h_reroot a r (f (f u r) c) d))).symm


private theorem band_symmetric (L : Assumptions f h) (r a b c d u : M) :
    (h r b (f (h r d (f (h r b (f (f u r) a)) c)) a)) = (h r b (f (h r d (f (f u r) c)) a)) := by
  calc
    _ = (h r b (f (h r d (f (f (h c b (f (f u r) a)) r) c)) a)) := (congrArg (fun q => (h r b (f (h r d q) a))) (L.h_reroot c r (f (f u r) a) b))
    _ = (h r b (f (h r d (f (f u r) c)) a)) := (band_source_root L r a b c d u)


private theorem band_native (L : Assumptions f h) (r a b c d u : M) :
    (h r (f (h r (f (h r (f (f u r) a) b) c) d) a) b) = (h r (f (h r (f (f u r) c) d) a) b) := by
  calc
    _ = (h r (f (h r (f (h r b (f (f u r) a)) c) d) a) b) := (congrArg (fun q => (h r (f (h r (f q c) d) a) b)) (L.h_sym r (f (f u r) a) b))
    _ = (h r (f (h r d (f (h r b (f (f u r) a)) c)) a) b) := (congrArg (fun q => (h r (f q a) b)) (L.h_sym r (f (h r b (f (f u r) a)) c) d))
    _ = (h r b (f (h r d (f (h r b (f (f u r) a)) c)) a)) := (L.h_sym r (f (h r d (f (h r b (f (f u r) a)) c)) a) b)
    _ = (h r b (f (h r d (f (f u r) c)) a)) := (band_symmetric L r a b c d u)
    _ = (h r (f (h r d (f (f u r) c)) a) b) := ((L.h_sym r (f (h r d (f (f u r) c)) a) b)).symm
    _ = (h r (f (h r (f (f u r) c) d) a) b) := ((congrArg (fun q => (h r (f q a) b)) (L.h_sym r (f (f u r) c) d))).symm


private theorem assumptions_of_models {M : Type u} [(Equational.language (Symbol Unit)).Structure M]
    (hm : Equational.Models fiveVariableTheory M) :
    Assumptions (resetOperation M) (guardedOperation M) where
  R1 r := by
    have hh := hm (fiveVariableAxiom 0) ⟨0, rfl⟩ ![r, r, r, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  R2 r a := by
    have hh := hm (fiveVariableAxiom 1) ⟨1, rfl⟩ ![r, a, r, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  R3 r a := by
    have hh := hm (fiveVariableAxiom 2) ⟨2, rfl⟩ ![r, a, r, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  R4 r a b := by
    have hh := hm (fiveVariableAxiom 3) ⟨3, rfl⟩ ![r, a, b, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  R5 r a b := by
    have hh := hm (fiveVariableAxiom 4) ⟨4, rfl⟩ ![r, a, b, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  R6 r a b := by
    have hh := hm (fiveVariableAxiom 5) ⟨5, rfl⟩ ![r, a, b, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  h_sym r a b := by
    have hh := hm (fiveVariableAxiom 6) ⟨6, rfl⟩ ![r, a, b, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  h_minor r a := by
    have hh := hm (fiveVariableAxiom 7) ⟨7, rfl⟩ ![r, a, r, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  h_root r a b := by
    have hh := hm (fiveVariableAxiom 8) ⟨8, rfl⟩ ![r, a, b, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  h_expand r a b u := by
    have hh := hm (fiveVariableAxiom 9) ⟨9, rfl⟩ ![r, a, b, r, r, u]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  h_back r a b u := by
    have hh := hm (fiveVariableAxiom 11) ⟨11, rfl⟩ ![r, a, b, r, r, u]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  h_reroot r a b u := by
    have hh := hm (fiveVariableAxiom 12) ⟨12, rfl⟩ ![r, a, b, r, r, u]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  h_insert r a b := by
    have hh := hm (fiveVariableAxiom 13) ⟨13, rfl⟩ ![r, a, b, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  project_join r a u v := by
    have hh := hm (fiveVariableAxiom 14) ⟨14, rfl⟩ ![r, a, r, r, v, u]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  reset_split a u v := by
    have hh := hm (fiveVariableAxiom 15) ⟨15, rfl⟩ ![a, a, a, a, v, u]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  root_preserve r u v := by
    have hh := hm (fiveVariableAxiom 16) ⟨16, rfl⟩ ![r, r, r, r, v, u]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  F_idem r a b u := by
    have hh := hm (fiveVariableAxiom 20) ⟨20, rfl⟩ ![r, a, b, r, r, u]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  F_cb r a b := by
    have hh := hm (fiveVariableAxiom 26) ⟨26, rfl⟩ ![r, a, b, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  terminal r a b := by
    have hh := hm (fiveVariableAxiom 29) ⟨29, rfl⟩ ![r, a, b, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  terminal_bound r a b := by
    have hh := hm (fiveVariableAxiom 30) ⟨30, rfl⟩ ![r, a, b, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  terminal_weak r a b := by
    have hh := hm (fiveVariableAxiom 31) ⟨31, rfl⟩ ![r, a, b, r, r, r]
    simpa [fiveVariableAxiom, basisAxiom] using hh
  exchange r u a b c := by
    have hh := hm (fiveVariableAxiom 21) ⟨21, rfl⟩ ![r, u, a, b, c]
    simpa [fiveVariableAxiom, exchangeAxiom] using hh

/-- Exchange recovers the unrestricted six-variable action-band law. -/
theorem action_band_of_models {M : Type u} [(Equational.language (Symbol Unit)).Structure M]
    (hm : Equational.Models fiveVariableTheory M) (r a b c d u : M) :
    guardedOperation M r (resetOperation M
      (guardedOperation M r (resetOperation M
        (guardedOperation M r (resetOperation M (resetOperation M u r) a) b) c) d) a) b =
    guardedOperation M r (resetOperation M
      (guardedOperation M r (resetOperation M (resetOperation M u r) c) d) a) b :=
  band_native (assumptions_of_models hm) r a b c d u

/-- Every model of the independent five-variable presentation satisfies the
complete word/action presentation. -/
theorem models_old {M : Type u} [(Equational.language (Symbol Unit)).Structure M]
    (hm : Equational.Models fiveVariableTheory M) : Equational.Models theory M := by
  rintro e ⟨i, rfl⟩
  by_cases hi : i = 21
  · subst i
    intro v
    change Fin 6 → M at v
    simpa [basisAxiom] using action_band_of_models hm (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
  · have hh := hm (fiveVariableAxiom i) ⟨i, rfl⟩
    simpa [fiveVariableAxiom, hi] using hh

end KFOL.Owner.FiniteBasis.FiveVariables

namespace KFOL.Owner.FiniteBasis.FiveVariables

universe u

/-- Exchange is a native five-variable identity of the four-state generator. -/
theorem exchange_holds : letI := fourStructure (Role := Unit); exchangeAxiom.Holds Four := by
  intro v
  change Fin 5 → Four at v
  change Four.guarded (v 0) (Four.guarded (v 0) (Four.reset (v 1) (v 2)) (v 3)) (v 4) =
    Four.guarded (v 0) (v 4) (Four.guarded (v 0) (Four.guarded (v 2) (v 1) (v 4)) (v 3))
  generalize v 0 = r
  generalize v 1 = u
  generalize v 2 = a
  generalize v 3 = b
  generalize v 4 = c
  cases r <;> cases u <;> cases a <;> cases b <;> cases c <;> rfl

theorem axiom_holds (i : Fin 36) :
    letI := fourStructure (Role := Unit); (fiveVariableAxiom i).Holds Four := by
  by_cases hi : i = 21
  · subst i
    simpa [fiveVariableAxiom] using exchange_holds
  · simpa [fiveVariableAxiom, hi] using basisAxiom_holds i

theorem models_four : letI := fourStructure (Role := Unit); Equational.Models fiveVariableTheory Four := by
  rintro e ⟨i, rfl⟩
  exact axiom_holds i

theorem axiom_injective : Function.Injective fiveVariableAxiom := by
  intro i j hij
  by_cases hi : i = 21
  · subst i
    by_contra hj
    have hj' : j ≠ 21 := Ne.symm hj
    have hh := congrArg Equational.Identity.arity hij
    simp [fiveVariableAxiom, hj', exchangeAxiom, basisAxiom] at hh
  · by_cases hj : j = 21
    · subst j
      have hh := congrArg Equational.Identity.arity hij
      simp [fiveVariableAxiom, hi, exchangeAxiom, basisAxiom] at hh
    · apply basisAxiom_injective
      simpa [fiveVariableAxiom, hi, hj] using hij

theorem theory_ncard : fiveVariableTheory.ncard = 36 := by
  rw [fiveVariableTheory, Set.ncard_range_of_injective axiom_injective, Nat.card_fin]

theorem variable_bound : Equational.HasVariableBound fiveVariableTheory 5 := by
  rintro e ⟨i, rfl⟩
  exact (show ∀ j : Fin 36, (fiveVariableAxiom j).variableCount ≤ 5 from by decide) i

/-- Thirty-six native equations on at most five distinct variables are a
complete basis, for arbitrary algebras and terms of arbitrary depth. -/
theorem isBasis : letI := fourStructure (Role := Unit); Equational.IsBasis Four fiveVariableTheory := by
  let _ := fourStructure (Role := Unit)
  intro e
  constructor
  · intro hv
    apply Equational.derives_of_valid_in_models fiveVariableTheory e.lhs e.rhs
    intro M _ _ hm v
    exact (((FiniteBasis.isBasis e).mp hv).sound M (models_old hm)) v
  · intro hd
    exact hd.sound Four models_four

/-- The five-variable presentation axiomatizes the intended one-owner algebra
for every carrier containing three distinct roles. -/
theorem isBasis_winnerSet {Role : Type u} (three : Fin 3 ↪ Role)
    (owner observer : Role) (ho : observer ≠ owner) :
    letI := oneOwnerStructure owner; Equational.IsBasis (WinnerSet Role) fiveVariableTheory := by
  intro e
  exact (winnerSet_holds_iff_four three owner observer ho e).trans (isBasis e)

end KFOL.Owner.FiniteBasis.FiveVariables
