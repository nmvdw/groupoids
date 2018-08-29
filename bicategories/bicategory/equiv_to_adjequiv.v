Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     bicategory.adjoint
     bicategory.equivalence.

Definition representable_faithful
           {C : BiCategory}
           {X Y Z : C}
           {f : C⟦X,Y⟧} {g : C⟦Y,X⟧}
           (η : id₁ X ==> g · f)
           (k₁ k₂ : C⟦Z,X⟧)
           (α β : k₁ ==> k₂)
           `{IsIsomorphism _ _ _ η}
  : f ◅ α = f ◅ β -> α = β.
Proof.
  intros Hαβ.
  rewrite (whisker_l_iso_id₁ η _ _ α).
  rewrite (whisker_l_iso_id₁ η _ _ β).
  rewrite (whisker_l_eq k₁ k₂ α β Hαβ).
  reflexivity.
Qed.

Definition representable_full
           {C : BiCategory}
           {X Y Z : C}
           {f : C⟦X,Y⟧} {g : C⟦Y,X⟧}
           (η : id₁ X ==> g · f)
           (θ : f · g ==> id₁ Y)
           `{IsIsomorphism _ _ _ η}
           (k₁ k₂ : C⟦Z,X⟧)
           (α : f · k₁ ==> f · k₂)
  : k₁ ==> k₂.
Proof.
  refine (_ ∘ left_unit_inv _).
  refine (_ ∘ η ▻ _).
  refine (_ ∘ assoc _ _ _).
  refine (_ ∘ g ◅ α).
  refine (_ ∘ assoc_inv _ _ _).
  refine (_ ∘ η^-1 ▻ k₂).
  apply left_unit.
Defined.

Definition full_spec
           {C : BiCategory}
           {X Y Z : C}
           {f : C⟦X,Y⟧} {g : C⟦Y,X⟧}
           (η : id₁ X ==> g · f)
           (θ : f · g ==> id₁ Y)
           `{IsIsomorphism _ _ _ η}
           `{IsIsomorphism _ _ _ θ}
           (k₁ k₂ : C⟦Z,X⟧)
           (α : f · k₁ ==> f · k₂)
  : f ◅ (representable_full η θ k₁ k₂ α) = α.
Proof.
  refine (representable_faithful θ^-1 (f · k₁) (f · k₂) _ α _).
  apply (vcomp_cancel_right (assoc _ _ _) _ _).
  rewrite <- whisker_l_hcomp.
  apply (vcomp_cancel_left (assoc_inv _ _ _) _ _).
  rewrite <- !vcomp_assoc.
  rewrite assoc_right, vcomp_left_identity.
  apply (vcomp_cancel_left (η^-1 ▻ k₂) _ _).
  apply (vcomp_cancel_left (left_unit k₂) _ _).
  apply (vcomp_cancel_right (η ▻ k₁) _ _).
  apply (vcomp_cancel_right (left_unit_inv k₁) _ _).
  rewrite <- !vcomp_assoc.
  rewrite <- whisker_l_iso_id₁.
  reflexivity.
Qed.

Section EquivToAdjEquiv.
  Context {C : BiCategory}
          {X Y : C}.
  Variable (f : C⟦X,Y⟧)
           (Hf : is_equivalence f).

  Local Definition g : C⟦Y,X⟧ := equiv_inv Hf.
  Local Definition η : id₁ X ==> g · f := (sect f Hf)^-1.
  Local Definition θ : f · g ==> id₁ Y := retr f Hf.

  Local Definition ε : f · g ==> id₁ Y.
  Proof.
    apply (representable_full θ^-1 η^-1).
    exact ((right_unit_inv g)
             ∘ left_unit g
             ∘ η^-1 ▻ g
             ∘ assoc_inv _ _ _).
  Defined.

  Definition equiv_to_adjequiv_d : is_left_adjoint_d f.
  Proof.
    make_is_left_adjoint.
    - exact (equiv_inv Hf).
    - exact (sect f Hf)^-1.
    - exact ε.
  Defined.

  Definition equiv_to_adjequiv_isadj : is_adjunction equiv_to_adjequiv_d.
  Proof.
    make_is_adjunction ; cbn ; unfold ε.
    - rewrite !vcomp_assoc.
      rewrite (full_spec _ _ _ _ _).
      rewrite <- !vcomp_assoc.
      rewrite right_unit_left, vcomp_left_identity.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
      rewrite assoc_right, vcomp_left_identity.
      rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite <- interchange.
      rewrite !vcomp_right_identity ; simpl.
      rewrite vcomp_right_inverse.
      rewrite hcomp_id₂.
      rewrite vcomp_left_identity.
      rewrite left_unit_left.
      reflexivity.
    - admit.
  Admitted.

  Definition equiv_to_adjequiv_left_adj : is_left_adjoint f
    := Build_is_left_adjoint equiv_to_adjequiv_d equiv_to_adjequiv_isadj.
  
  Definition equiv_to_adjequiv
    : X ≃ Y
    := Build_adjoint_equivalence equiv_to_adjequiv_left_adj _ _.
End EquivToAdjEquiv.

Definition comp_adjequiv
           {C : BiCategory}
           {X Y Z : C}
  : X ≃ Y -> Y ≃ Z -> X ≃ Z
  := fun f₁ f₂ => equiv_to_adjequiv (f₂ · f₁) (comp_isequiv f₂ f₁).