Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     bicategory.adjoint
     bicategory.equivalence.

Definition banaan
           `{Funext}
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧) (g g' : C⟦Y,X⟧)
           (η : id₁ X ==> g · f)
           (η' : id₁ X ==> g' · f)
  : ((g · f) ◅ (η' ▻ g ∘ left_unit_inv _))
      ∘ η ▻ g
    = (η ▻ (g' · f · g) ∘ left_unit_inv _)
        ∘ η' ▻ g.
Proof.
  rewrite bc_whisker_l_compose.
  unfold bc_whisker_l, bc_whisker_r.
  rewrite !vcomp_assoc.
  rewrite left_unit_inv_natural.
  rewrite <- !vcomp_assoc.
  rewrite <- !interchange.
  rewrite !vcomp_right_identity, !vcomp_left_identity.
  rewrite <- (vcomp_right_identity η).
  rewrite interchange.
  rewrite vcomp_right_identity.
  f_ap.
  rewrite left_unit_inv_assoc₂.
  rewrite <- triangle_l_inv.
  rewrite <- right_unit_V_id_is_left_unit_V_id.
  reflexivity.
Qed.

Definition test
           `{Funext}
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧) (g g' : C⟦Y,X⟧)
           (η : id₁ X ==> g · f)
           (η' : id₁ X ==> g' · f)
  : g ◅ ((f ◅ η') ▻ g)
      ∘ (g ◅ (right_unit_inv f ▻ g)
      ∘ (assoc _ _ _
      ∘ η ▻ g))
    = g ◅ (assoc_inv _ _ _)
        ∘ assoc _ _ _
        ∘ η ▻ (g' · f · g)
        ∘ left_unit_inv _
        ∘ η' ▻ g.
Proof.
  pose @banaan.
  rewrite !vcomp_assoc.
  rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
  rewrite <- banaan.
  rewrite <- !vcomp_assoc.
  f_ap.
  rewrite bc_whisker_l_compose.
  unfold bc_whisker_l, bc_whisker_r.
  rewrite !vcomp_assoc.
  rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
  rewrite <- hcomp_id₂.
  rewrite assoc_natural.
  rewrite !vcomp_assoc.
  rewrite assoc_natural.
  rewrite <- !vcomp_assoc.
  f_ap.
  rewrite <- !interchange.
  rewrite !vcomp_right_identity.
  rewrite assoc_inv_natural.
  rewrite !vcomp_assoc.
  rewrite <- (vcomp_left_identity (id₂ g)).
  rewrite !interchange.
  rewrite triangle_r_inv.
  rewrite vcomp_left_identity.
  reflexivity.
Qed.

Definition adjoint_unique_map
           `{Funext}
           {C : BiCategory}
           {X Y : C}
           (l : C⟦X,Y⟧)
           (A₁ : is_left_adjoint l)
           (A₂ : is_left_adjoint l)
  : right_adjoint A₁ ==> right_adjoint A₂
  := right_unit _ ∘ _ ◅ counit A₁ ∘ assoc _ _ _ ∘ unit A₂ ▻ _ ∘ left_unit_inv _.

Section AdjointUniqueMapCompose.
  Context `{Funext}
          {C : BiCategory}
          {X Y : C}.
  Variable (l : C⟦X,Y⟧)
           (A₁ : is_left_adjoint l)
           (A₂ : is_left_adjoint l).

  Local Notation r₁ := (right_adjoint A₁).
  Local Notation r₂ := (right_adjoint A₂).
  Local Notation η₁ := (unit A₁).
  Local Notation η₂ := (unit A₂).
  Local Notation ε₁ := (counit A₁).
  Local Notation ε₂ := (counit A₂).

  Local Notation r₁_to_r₂ := (adjoint_unique_map l A₁ A₂).

  Local Notation r₂_to_r₁ := (adjoint_unique_map l A₂ A₁).

  Local Definition composition_of_triangles : r₁ ==> r₁
    := (right_unit r₁)
         ∘ r₁ ◅ ε₁
         ∘ assoc r₁ l r₁
         ∘ (r₁ ◅ ((left_unit l)
                    ∘ ε₂ ▻ l
                    ∘ assoc_inv l r₂ l
                    ∘ l ◅ η₂
                    ∘ right_unit_inv l) ∘ η₁) ▻ r₁
         ∘ left_unit_inv r₁.

  Local Definition composition_of_triangles_is_identity
    : composition_of_triangles = id₂ r₁.
  Proof.
    unfold composition_of_triangles.
    rewrite unit_counit_r.
    unfold bc_whisker_l.
    rewrite hcomp_id₂, vcomp_left_identity.
    apply unit_counit_l.
  Qed.

  Local Definition ε₁_natural
    : ε₁ ∘ (left_unit l ∘ ε₂ * id₂ l) * id₂ r₁
      =
      ε₂ ∘ l ◅ (right_unit r₂ ∘ r₂ ◅ ε₁) ∘ assoc l r₂ (l · r₁) ∘ assoc (l · r₂) l r₁.
  Proof.
    rewrite bc_whisker_l_compose.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite <- assoc_natural.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- right_unit_assoc.
    rewrite <- !vcomp_assoc.
    rewrite <- right_unit_natural.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- !interchange.
    rewrite !hcomp_id₂, vcomp_left_identity, vcomp_right_identity.
    rewrite <- (vcomp_right_identity ε₁).
    rewrite <- (vcomp_left_identity ε₂).
    rewrite interchange.
    rewrite <- !vcomp_assoc, !vcomp_left_identity, !vcomp_right_identity.
    rewrite right_unit_id_is_left_unit_id.
    rewrite left_unit_natural.
    rewrite !vcomp_assoc.
    rewrite <- hcomp_id₂.
    rewrite <- assoc_natural.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- left_unit_assoc.
    unfold bc_whisker_r.
    rewrite <- interchange.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.
    
  Local Definition composition_of_maps : r₂_to_r₁ ∘ r₁_to_r₂ = composition_of_triangles.
  Proof.
    unfold r₁_to_r₂, r₂_to_r₁, composition_of_triangles.
    rewrite !vcomp_assoc.
    f_ap.
    rewrite <- !vcomp_assoc.
    f_ap.
    rewrite !bc_whisker_l_compose, !bc_whisker_r_compose.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite assoc_natural.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite assoc_natural.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ z))) (vcomp_assoc _ _ _)^).
    rewrite assoc_natural.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ (_ ∘ z)))) (vcomp_assoc _ _ _)^).
    rewrite assoc_natural.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ (_ ∘ (_ ∘ z))))) (vcomp_assoc _ _ _)^).
    rewrite assoc_natural.
    rewrite !vcomp_assoc.
    rewrite test.
    rewrite <- !vcomp_assoc.
    f_ap.
    rewrite <- !interchange.
    rewrite !vcomp_assoc.
    fold r₂.
    rewrite <- inverse_pentagon_3.
    rewrite <- !vcomp_assoc.
    do 3 rewrite interchange.
    rewrite !vcomp_right_identity.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ z))) (vcomp_assoc _ _ _)^).
    rewrite <- assoc_natural.
    rewrite <- interchange.
    rewrite !hcomp_id₂.
    rewrite !vcomp_assoc, vcomp_right_identity.
    rewrite ε₁_natural.
    rewrite !bc_whisker_l_compose.
    repeat (rewrite <- (vcomp_left_identity (id₂ r₁)) ; rewrite interchange).
    rewrite !vcomp_left_identity.
    rewrite !vcomp_assoc.
    f_ap.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ z))) (vcomp_assoc _ _ _)^).
    rewrite <- bc_whisker_l_compose.
    rewrite assoc_left.
    unfold bc_whisker_l.
    rewrite hcomp_id₂, vcomp_left_identity.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite <- bc_whisker_l_compose.
    rewrite assoc_left.
    unfold bc_whisker_l.
    rewrite hcomp_id₂, vcomp_left_identity.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- assoc_natural.
    rewrite <- !vcomp_assoc.
    rewrite <- assoc_natural.
    rewrite !vcomp_assoc.
    f_ap.
    rewrite !hcomp_id₂.
    rewrite <- !vcomp_assoc.
    rewrite <- !interchange.
    rewrite !vcomp_assoc, !vcomp_right_identity, !vcomp_left_identity.
    rewrite <- (vcomp_left_identity (right_unit r₂)).
    rewrite !vcomp_assoc.
    rewrite <- (vcomp_right_identity η₁).
    rewrite interchange.
    rewrite !vcomp_assoc.
    rewrite !vcomp_left_identity, !vcomp_right_identity.
    f_ap.
    rewrite left_unit_inv_natural.
    reflexivity.
  Qed.
End AdjointUniqueMapCompose.

Section UniquenessAdjoint.
  Context `{Funext}
          {C : BiCategory}
          {X Y : C}.
  Variable (l : C⟦X,Y⟧)
           (A₁ : is_left_adjoint l)
           (A₂ : is_left_adjoint l).

  Local Notation r₁ := (right_adjoint A₁).
  Local Notation r₂ := (right_adjoint A₂).
  Local Notation η₁ := (unit A₁).
  Local Notation η₂ := (unit A₂).
  Local Notation ε₁ := (counit A₁).
  Local Notation ε₂ := (counit A₂).

  Local Notation r₁_to_r₂ := (adjoint_unique_map l A₁ A₂).

  Local Notation r₂_to_r₁ := (adjoint_unique_map l A₂ A₁).

  Global Instance adjoint_unique_map_iso
    : isomorphism_2cell r₁_to_r₂.
  Proof.
    simple refine (Build_isomorphism_2cell _ _ _).
    - exact r₂_to_r₁.
    - rewrite composition_of_maps.
      apply composition_of_triangles_is_identity.
    - rewrite composition_of_maps.
      apply composition_of_triangles_is_identity.
  Defined.
End UniquenessAdjoint.