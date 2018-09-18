Require Import HoTT.
Require Import GR.bicategories.bicategories.
Require Import GR.bicategories.lax_functors.
Require Import GR.bicategories.lax_transformations.
Require Import GR.bicategories.modifications.
Require Import GR.bicategories.biadjunction.biadjunction.

Definition laxnaturality_of_triangle_l_lhs
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction_d C D)
           {X Y : C}
           (f : C⟦X,Y⟧)
  : laxnaturality_of (triangle_l_lhs F) f
    =
    (assoc_inv _ _ _)
      ∘ (_ ◅ (left_unit_inv _ ∘ right_unit _))
      ∘ assoc _ _ _
      ∘ ((assoc_inv _ _ _)
           ∘ _ ◅ ((Fcomp₁_inv _ _ _)
                    ∘ (_ ₂ (laxnaturality_of (unit_d F) f))
                    ∘ Fcomp₁ _ _ _)
           ∘ assoc _ _ _
           ∘ ((assoc_inv _ _ _)
                ∘ _ ◅ (left_unit_inv _ ∘ right_unit _)
                ∘ assoc _ _ _
                ∘ ((assoc_inv _ _ _)
                     ∘ _ ◅ (laxnaturality_of (counit_d F) _)
                     ∘ assoc _ _ _
                     ∘ (left_unit_inv _ ∘ right_unit _) ▻ _
                     ∘ assoc_inv _ _ _) ▻ _
                ∘ assoc_inv _ _ _) ▻ _
           ∘ assoc_inv _ _ _) ▻ _
      ∘ assoc_inv _ _ _.
Proof.
  reflexivity.
Qed.

Section Restriction.
  Context `{Univalence}
          {C D : BiCategory}.
  Variable (adj : BiAdjunction C D)
           (P : C -> hProp)
           (HP : forall (x : D), P(right_adjoint adj x)).

  Definition restriction_left_adjoint := lax_restriction (left_adjoint adj) P.

  Definition restriction_right_adjoint := lax_factor (right_adjoint adj) P HP.

  Definition restriction_unit_d
    : LaxTransformation_d
        (lax_id_functor (full_sub C P))
        (lax_comp restriction_right_adjoint restriction_left_adjoint).
  Proof.
    make_lax_transformation.
    - exact (fun X => unit adj X.1).
    - exact (fun X Y f => laxnaturality_of (unit adj) f).
  Defined.

  Definition is_lax_restriction_unit_d
    : is_lax_transformation restriction_unit_d.
  Proof.
    make_is_lax_transformation.
    - intros X Y f g α ; simpl in *.
      exact (laxnaturality_natural (unit adj) α).
    - intros X.
      exact (transformation_unit (unit adj) X.1).
    - intros X Y Z f g.
      exact (transformation_assoc (unit adj) f g).
  Qed.

  Definition restriction_unit
    : LaxTransformation
        (lax_id_functor (full_sub C P))
        (lax_comp restriction_right_adjoint restriction_left_adjoint)
    := Build_LaxTransformation restriction_unit_d is_lax_restriction_unit_d.

  Definition restriction_counit_d
    : LaxTransformation_d
        (lax_comp restriction_left_adjoint restriction_right_adjoint)
        (lax_id_functor D).
  Proof.
    make_lax_transformation.
    - exact (counit adj).
    - intros X Y f ; cbn.
      exact (laxnaturality_of (counit adj) f).
  Defined.

  Definition is_lax_restriction_counit_d
    : is_lax_transformation restriction_counit_d.
  Proof.
    make_is_lax_transformation.
    - intros X Y f g p.
      exact (laxnaturality_natural (counit adj) p).
    - intros X ; simpl.
      exact (transformation_unit (counit adj) X).
    - intros X Y Z f g.
      exact (transformation_assoc (counit adj) f g).
  Qed.

  Definition restriction_counit
    : LaxTransformation
        (lax_comp restriction_left_adjoint restriction_right_adjoint)
        (lax_id_functor D)
    := Build_LaxTransformation restriction_counit_d is_lax_restriction_counit_d.

  Definition restrict_adjunction_d : BiAdjunction_d (full_sub C P) D
    := Build_BiAdjunction_d
         restriction_left_adjoint
         _
         restriction_right_adjoint
         _
         restriction_unit
         restriction_counit.

  Local Notation restriction_triangle_l_d
    := (fun (A : (full_sub C P)) =>
          mod_component (adj_triangle_l adj) A.1
          : (triangle_l_lhs restrict_adjunction_d A)
              ==>
              identity_transformation (left_adjoint_d restrict_adjunction_d) A).

  Lemma help_restriction_triangle_l
        {X Y : full_sub C P}
        (f : full_sub C P ⟦X,Y⟧)
    : Fcomp₁_inv (left_adjoint_d adj.1) ((unit_d adj.1) Y.1) f
      =
      Fcomp₁_inv restriction_left_adjoint (restriction_unit Y) f.
  Proof.
    cbn.
    compute.
    apply path_inverse.
    reflexivity.
  Qed.

  Definition restriction_triangle_l_is_mod
    : is_modification restriction_triangle_l_d.
  Proof.
    intros X Y f.
    exact (mod_commute (adj_triangle_l adj) f).
  Defined.

  Definition restriction_triangle_l
    : IsoModification
        (triangle_l_lhs restrict_adjunction_d)
        (identity_transformation (left_adjoint_d restrict_adjunction_d)).
  Proof.
    make_iso_modification.
    - exact (Build_Modification restriction_triangle_l_d restriction_triangle_l_is_mod).
    - intros [X PX] ; cbn in *.
      exact (iso_mod_component_is_iso (adj_triangle_l adj) X).
  Defined.

  Local Notation restriction_triangle_r_d
    := (fun (A : D) =>
          mod_component (adj_triangle_r adj) A
          : (triangle_r_lhs restrict_adjunction_d A)
              ==> identity_transformation (right_adjoint_d restrict_adjunction_d) A).
  
  Definition restriction_triangle_r_is_mod
    : is_modification restriction_triangle_r_d.
  Proof.
    intros X Y f.
    exact (mod_commute (adj_triangle_r adj) f).
  Defined.

  Definition restriction_triangle_r
    : IsoModification
        (triangle_r_lhs restrict_adjunction_d)
        (identity_transformation (right_adjoint_d restrict_adjunction_d)).
  Proof.
    make_iso_modification.
    - exact (Build_Modification restriction_triangle_r_d restriction_triangle_r_is_mod).
    - intros X ; cbn in *.
      exact (iso_mod_component_is_iso (adj_triangle_r adj) X).
  Defined.

  Definition restrict_adjunction : BiAdjunction (full_sub C P) D.
  Proof.
    simple refine (Build_BiAdjunction restrict_adjunction_d _).
    make_is_biadjunction.
    - intros X Y f ; cbn in *.
      apply adj.
    - intros X Y f ; cbn in *.
      apply adj.
    - exact restriction_triangle_l.
    - exact restriction_triangle_r.
  Defined.
End Restriction.
