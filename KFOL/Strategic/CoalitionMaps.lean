module

public import KFOL.Definitions.CoalitionGames
public import KFOL.Algebra.CoalitionMapsImages
public import KFOL.Strategic.Adequacy

/-! # Exactly which coalition maps descend to public-game values -/

@[expose] public section

namespace KFOL.CoalitionMaps

universe u v

variable {Role : Type u} {Team : Type v}

theorem Intertwines.value_mapRoles (f : Role → Team)
    {h : WinnerSet Role → WinnerSet Team} (hh : Intertwines f h)
    (G : Strategic.Tree Role) :
    h (Strategic.value G) = Strategic.value (G.mapRoles f) := by
  induction G with
  | leaf r => simpa [Strategic.Tree.mapRoles] using hh.1 r
  | node r G H hG hH =>
    simp only [Strategic.Tree.mapRoles, Strategic.value_node, hh.2, hG, hH]

theorem gameDescends_of_descends (f : Role → Team) (hf : Descends f) : GameDescends f := by
  obtain ⟨h, hh⟩ := hf
  intro G H he
  have hv : Strategic.value G = Strategic.value H := Subtype.ext he
  change (Strategic.value (G.mapRoles f)).val = (Strategic.value (H.mapRoles f)).val
  apply congrArg (fun A : WinnerSet Team => A.val)
  rw [← hh.value_mapRoles f G, ← hh.value_mapRoles f H, hv]

theorem GameDescends.value_mapRoles_eq (f : Role → Team) (hf : GameDescends f)
    {G H : Strategic.Tree Role} (he : Strategic.value G = Strategic.value H) :
    Strategic.value (G.mapRoles f) = Strategic.value (H.mapRoles f) :=
  Subtype.ext (hf G H (congrArg Subtype.val he))

theorem exists_two_leaf_game_obstruction (f : Role → Team) (hf : ¬Descends f) :
    ∃ a b c d,
      Strategic.possibleWinners (.node a (.leaf b) (.leaf c)) =
        Strategic.possibleWinners (.node d (.leaf b) (.leaf c)) ∧
      Strategic.possibleWinners ((Strategic.Tree.node a (.leaf b) (.leaf c)).mapRoles f) ≠
        Strategic.possibleWinners ((Strategic.Tree.node d (.leaf b) (.leaf c)).mapRoles f) := by
  obtain ⟨a, b, c, d, he, hn⟩ := exists_two_leaf_obstruction f hf
  refine ⟨a, b, c, d, ?_, ?_⟩
  · change (Strategic.value (.node a (.leaf b) (.leaf c))).val =
      (Strategic.value (.node d (.leaf b) (.leaf c))).val
    simpa using congrArg Subtype.val he
  · intro he
    apply hn
    have hv : Strategic.value ((Strategic.Tree.node a (.leaf b) (.leaf c)).mapRoles f) =
        Strategic.value ((Strategic.Tree.node d (.leaf b) (.leaf c)).mapRoles f) :=
      Subtype.ext he
    simpa [Strategic.Tree.mapRoles] using hv

/-- Every failure of algebraic descent already has a finite game witness,
even when the ambient role types are infinite. -/
theorem gameDescends_iff_descends (f : Role → Team) : GameDescends f ↔ Descends f := by
  classical
  constructor
  · intro hf
    by_contra hn
    obtain ⟨a, b, c, d, he, hne⟩ := exists_two_leaf_game_obstruction f hn
    exact hne (hf (.node a (.leaf b) (.leaf c)) (.node d (.leaf b) (.leaf c)) he)
  · exact gameDescends_of_descends f

/-- The complete coalition-map classification is about actual equilibrium
winner sets, not merely the backward-induction recurrence. -/
theorem gameDescends_iff (f : Role → Team) : GameDescends f ↔ Admissible f :=
  (gameDescends_iff_descends f).trans (descends_iff f)

/-- The exceptional two-team map keeps exactly the forced-win bit of its
singleton block, even when that map is non-injective. -/
theorem value_mapRoles_singletonBlock (f : Role → Team) (c : Role) (q : Team)
    (hc : f c ≠ q) (hothers : ∀ r, r ≠ c → f r = q) (G : Strategic.Tree Role) :
    Strategic.value (G.mapRoles f) =
      if Strategic.value G = WinnerSet.singleton c then WinnerSet.singleton (f c)
        else WinnerSet.singleton q :=
  ((collapse_intertwines f c q hc hothers).value_mapRoles f G).symm

theorem value_mapRoles_of_injective (f : Role → Team) (hf : Function.Injective f)
    (G : Strategic.Tree Role) :
    Strategic.value (G.mapRoles f) = image f (Strategic.value G) :=
  ((image_intertwines f hf).value_mapRoles f G).symm

/-- The old winner observation is always a sound upper bound after team
formation, including maps which do not descend to any value operation. -/
theorem value_mapRoles_subset_image (f : Role → Team) (G : Strategic.Tree Role) :
    (Strategic.value (G.mapRoles f)).val ⊆ (image f (Strategic.value G)).val := by
  induction G with
  | leaf r => simp [Strategic.Tree.mapRoles]
  | node r G H hG hH =>
    simpa only [Strategic.Tree.mapRoles, Strategic.value_node] using
      choice_subset_image f r (Strategic.value G) (Strategic.value H)
        (Strategic.value (G.mapRoles f)) (Strategic.value (H.mapRoles f)) hG hH

/-- Every winner value has a game representative, which makes a descended
value map unique. -/
theorem intertwiner_unique [Finite Role] (three : Fin 3 ↪ Role) (f : Role → Team)
    {h k : WinnerSet Role → WinnerSet Team} (hh : Intertwines f h)
    (hk : Intertwines f k) : h = k := by
  funext A
  obtain ⟨G, hG⟩ := Strategic.exists_value_of_finite three A (Set.toFinite A.val)
  rw [← hG, hh.value_mapRoles f G, hk.value_mapRoles f G]

end KFOL.CoalitionMaps
