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
           `{isomorphism_2cell _ _ _ _ _ η}
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
           `{isomorphism_2cell _ _ _ _ _ η}
           (k₁ k₂ : C⟦Z,X⟧)
           (α : f · k₁ ==> f · k₂)
  : k₁ ==> k₂.
Proof.
  refine (_ ∘ left_unit_inv _).
  refine (_ ∘ η ▻ _).
  refine (_ ∘ assoc _ _ _).
  refine (_ ∘ g ◅ α).
  refine (_ ∘ assoc_inv _ _ _).
  refine (_ ∘ (η^-1)%bicategory ▻ k₂).
  apply left_unit.
Defined.

Definition full_spec
           {C : BiCategory}
           {X Y Z : C}
           {f : C⟦X,Y⟧} {g : C⟦Y,X⟧}
           (η : id₁ X ==> g · f)
           (θ : f · g ==> id₁ Y)
           `{isomorphism_2cell _ _ _ _ _ η}
           `{isomorphism_2cell _ _ _ _ _ θ}
           (k₁ k₂ : C⟦Z,X⟧)
           (α : f · k₁ ==> f · k₂)
  : f ◅ (representable_full η θ k₁ k₂ α) = α.
Proof.
  refine (representable_faithful (θ^-1)%bicategory (f · k₁) (f · k₂) _ α _).
  apply (vcomp_cancel_right (assoc _ _ _) _ _).
  rewrite <- whisker_l_hcomp.
  apply (vcomp_cancel_left (assoc_inv _ _ _) _ _).
  rewrite <- !vcomp_assoc.
  rewrite assoc_right, vcomp_left_identity.
  apply (vcomp_cancel_left (η^-1%bicategory ▻ k₂) _ _).
  apply (vcomp_cancel_left (left_unit k₂) _ _).
  apply (vcomp_cancel_right (η ▻ k₁) _ _).
  apply (vcomp_cancel_right (left_unit_inv k₁) _ _).
  rewrite <- !vcomp_assoc.
  rewrite <- whisker_l_iso_id₁.
  reflexivity.
Qed.

Section EquivToAdjEquiv.
  Context `{Funext}
          {C : BiCategory}
          {X Y : C}.
  Variable (f : C⟦X,Y⟧)
           (Hf : is_equivalence f).

  Local Definition g : C⟦Y,X⟧ := equiv_inv Hf.
  Local Definition η : id₁ X ==> g · f := (sect f Hf)^-1%bicategory.
  Local Definition θ : f · g ==> id₁ Y := retr f Hf.

  Local Definition ε : f · g ==> id₁ Y.
  Proof.
    apply (representable_full θ^-1%bicategory η^-1%bicategory).
    exact ((right_unit_inv g)
             ∘ left_unit g
             ∘ η^-1%bicategory ▻ g
             ∘ assoc_inv _ _ _).
  Defined.

  Definition equiv_to_adjequiv_d : is_left_adjoint_d f.
  Proof.
    make_is_left_adjoint.
    - exact (equiv_inv Hf).
    - exact (sect f Hf)^-1.
    - exact ε.
  Defined.

  Local Definition first_triangle_law
    : (right_unit g)
        ∘ g ◅ ε
        ∘ assoc g f g
        ∘ η ▻ g
        ∘ left_unit_inv _
      = id₂ g.
  Proof.
    rewrite !vcomp_assoc.
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
  Qed.
  
  Definition whisker_ηg
    : η ▻ g = (right_unit g ∘ g ◅ ε ∘ assoc g f g)^-1%bicategory ∘ left_unit g.
  Proof.
    refine (vcomp_move_L_Mp _ _ _ _).
    rewrite <- (vcomp_left_identity (left_unit g)).
    refine (vcomp_move_L_pM _ _ _ _).
    apply first_triangle_law.
  Qed.

  Local Definition η_natural
    : η ▻ (g · f) ∘ left_unit_inv (g · f) ∘ η
      =
      (g · f) ◅ η ∘ right_unit_inv (g · f) ∘ η.
  Proof.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite !vcomp_assoc.
    rewrite left_unit_inv_natural, right_unit_inv_natural.
    rewrite <- !vcomp_assoc.
    rewrite <- !interchange.
    rewrite !vcomp_right_identity, !vcomp_left_identity.
    rewrite right_unit_V_id_is_left_unit_V_id.
    reflexivity.
  Qed.

  Local Definition η_natural_help
    : η ▻ (g · f) ∘ left_unit_inv (g · f)
      =
      (g · f) ◅ η ∘ right_unit_inv (g · f)
    := vcomp_cancel_right η _ _ η_natural.

  Local Definition η_whisker_l_hcomp
    : (g · f) ◅ η = assoc_inv g f (g · f) ∘ g ◅ (f ◅ η) ∘ assoc g f (id₁ X).
  Proof.
    rewrite !vcomp_assoc.
    refine (vcomp_move_L_Mp _ _ _ _) ; simpl.
    unfold bc_whisker_l.
    rewrite <- hcomp_id₂.
    rewrite assoc_natural.
    reflexivity.
  Qed.

  Local Definition η_whisker_r_hcomp
    : η ▻ (g · f) = assoc (g · f) g f ∘ η ▻ g ▻ f ∘ assoc_inv (id₁ X) g f.
  Proof.
    refine (vcomp_move_L_pM _ _ _ _) ; simpl.
    rewrite assoc_natural.
    rewrite hcomp_id₂.
    reflexivity.
  Qed.

  Local Definition help1
    : assoc (g · f) g f ∘ (η ▻ g ∘ left_unit_inv _) ▻ f
      =
      (assoc_inv g f (g · f))
        ∘ g ◅ (f ◅ η)
        ∘ assoc g f (id₁ X)
        ∘ right_unit_inv (g · f).
  Proof.
    rewrite <- η_whisker_l_hcomp.
    rewrite bc_whisker_r_compose.
    rewrite left_unit_inv_assoc.
    rewrite <- !vcomp_assoc.
    rewrite assoc_natural.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite assoc_left, vcomp_left_identity.
    rewrite hcomp_id₂.
    exact η_natural_help.
  Qed.

  Local Definition help2
    : g ◅ (assoc f g f ∘ ε^-1%bicategory ▻ f ∘ left_unit_inv _)
      =
      g ◅ (f ◅ η ∘ right_unit_inv f).
  Proof.
    rewrite !bc_whisker_l_compose.
    rewrite !vcomp_assoc.
    unfold bc_whisker_l.
    rewrite <- triangle_l_inv.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- assoc_natural.
    pose help1 as p.
    rewrite whisker_ηg in p.
    rewrite !vcomp_inverse in p.
    rewrite !vcomp_assoc in p.
    rewrite left_unit_left, vcomp_right_identity in p.
    rewrite !bc_whisker_r_compose in p.
    rewrite <- !vcomp_assoc in p.
    rewrite right_unit_inv_assoc in p.
    rewrite !vcomp_assoc in p.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^) in p.
    rewrite assoc_left, vcomp_left_identity in p.
    rewrite <- bc_whisker_l_compose in p.
    rewrite <- !vcomp_assoc in p.
    rewrite inverse_pentagon_5 in p.
    rewrite !vcomp_assoc in p.
    refine (vcomp_cancel_left (assoc_inv g f (g · f)) _ _ _).
    rewrite !vcomp_assoc.
    rewrite <- !bc_whisker_l_compose.
    exact p.
  Qed.

  Local Definition help3
    : assoc f g f ∘ ε^-1%bicategory ▻ f ∘ left_unit_inv f
      =
      f ◅ η ∘ right_unit_inv f.
  Proof.
    refine (representable_faithful _ _ _ _ _ help2).
    apply (equivalence_inv (Build_Equivalence f Hf)).
  Qed.

  Definition equiv_to_adjequiv_isadj : is_adjunction equiv_to_adjequiv_d.
  Proof.
    make_is_adjunction ; cbn.
    - exact first_triangle_law.
    - rewrite !vcomp_assoc.
      rewrite <- help3.
      rewrite !vcomp_assoc.
      rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
      rewrite assoc_right, vcomp_left_identity.
      rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
      rewrite <- bc_whisker_r_compose.
      rewrite vcomp_right_inverse.
      unfold bc_whisker_r.
      rewrite hcomp_id₂, vcomp_left_identity.
      rewrite left_unit_left.
      reflexivity.
  Defined.

  Definition equiv_to_adjequiv_left_adj : is_left_adjoint f
    := Build_is_left_adjoint equiv_to_adjequiv_d equiv_to_adjequiv_isadj.
  
  Definition equiv_to_adjequiv
    : X ≃ Y
    := Build_adjoint_equivalence equiv_to_adjequiv_left_adj _ _.
End EquivToAdjEquiv.

Definition comp_adjequiv
           `{Funext}
           {C : BiCategory}
           {X Y Z : C}
  : X ≃ Y -> Y ≃ Z -> X ≃ Z
  := fun f₁ f₂ => equiv_to_adjequiv (f₂ · f₁) (comp_isequiv f₂ f₁).