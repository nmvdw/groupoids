Require Import HoTT.
Require Import HoTT.Categories.Category.
From GR.bicategories Require Import
     bicategory.bicategory_laws
     bicategory.adjoint
     bicategory.equivalence
     bicategory.univalent.

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
    
  Definition composition_of_maps : r₂_to_r₁ ∘ r₁_to_r₂ = composition_of_triangles.
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
    : IsIsomorphism r₁_to_r₂.
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact r₂_to_r₁.
    - pose @composition_of_maps as p.
      pose @composition_of_triangles_is_identity as q.
      unfold vcomp in *.
      rewrite p, q.
      reflexivity.
    - pose @composition_of_maps as p.
      pose @composition_of_triangles_is_identity as q.
      unfold vcomp in *.
      rewrite p, q.
      reflexivity.
  Defined.

  Definition remove_η₂
    : r₂ ◅ (left_unit l ∘ ε₁ ▻ l ∘ assoc_inv l r₁ l ∘ l ◅ η₁)
         ∘ assoc r₂ l (id₁ X)
         ∘ right_unit_inv (r₂ · l)
         ∘ η₂
      = η₂.
  Proof.
    refine (_ @ vcomp_left_identity _).
    f_ap.
    rewrite <- hcomp_id₂.
    rewrite <- (unit_counit_r A₁).
    pose @bc_whisker_l_compose as p.
    unfold bc_whisker_l in *.
    rewrite !p.
    rewrite !vcomp_assoc.
    repeat f_ap.
    rewrite right_unit_inv_assoc.
    rewrite <- !vcomp_assoc.
    rewrite assoc_left, vcomp_left_identity.
    reflexivity.
  Qed.

  Definition help_triangle_η
    : (η₂ ▻ r₁) ▻ l ∘ (left_unit_inv r₁ ▻ l ∘ η₁)
      =
      (assoc_inv (r₂ · l) r₁ l)
        ∘ assoc_inv r₂ l (r₁ · l)
        ∘ r₂ ◅ (l ◅ η₁)
        ∘ assoc r₂ l (id₁ X)
        ∘ right_unit_inv (r₂ · l) ∘ η₂.
  Proof.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite <- assoc_natural.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite assoc_right, vcomp_left_identity.
    rewrite !vcomp_assoc.
    refine (vcomp_move_L_Mp _ _ _ _) ; simpl.
    rewrite right_unit_inv_natural.
    rewrite <- !vcomp_assoc.
    rewrite <- interchange, vcomp_right_identity, hcomp_id₂, vcomp_left_identity.
    rewrite assoc_natural, hcomp_id₂.
    rewrite right_unit_V_id_is_left_unit_V_id.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- left_unit_inv_assoc₂.
    rewrite left_unit_inv_natural.
    rewrite <- !vcomp_assoc.
    f_ap.
    rewrite <- interchange.
    rewrite !vcomp_left_identity, vcomp_right_identity.
    reflexivity.
  Qed.

  Definition transport_unit
    : r₁_to_r₂ ▻ l ∘ η₁ = η₂.
  Proof.
    rewrite <- remove_η₂.
    unfold r₁_to_r₂.
    rewrite !bc_whisker_r_compose.
    rewrite !vcomp_assoc.
    rewrite help_triangle_η.
    rewrite right_unit_inv_assoc.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ (_ ∘ (_ ∘ (_ ∘ z)))))) (vcomp_assoc _ _ _)^).
    rewrite assoc_left, vcomp_left_identity.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ (_ ∘ (_ ∘ z))))) (vcomp_assoc _ _ _)^).
    rewrite <- bc_whisker_l_compose.
    rewrite <- !vcomp_assoc.
    rewrite !bc_whisker_l_compose.
    repeat f_ap.
    rewrite <- !vcomp_assoc.
    f_ap.
    rewrite !vcomp_assoc.
    rewrite assoc_left, vcomp_right_identity.
    rewrite <- !vcomp_assoc.
    f_ap.
    rewrite !vcomp_assoc.
    rewrite inverse_pentagon.
    rewrite <- !vcomp_assoc.
    f_ap.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite <- !bc_whisker_r_compose.
    rewrite assoc_left.
    unfold bc_whisker_r.
    rewrite hcomp_id₂, vcomp_left_identity.
    rewrite <- assoc_inv_natural.
    rewrite <- !vcomp_assoc.
    f_ap.
    apply triangle_l.
  Qed.

  Definition help_triangle_ε
    : ε₂ ∘ l ◅ (right_unit r₂ ∘ r₂ ◅ ε₁)
      = ε₁ ∘ left_unit (l · r₁)
           ∘ assoc _ _ _
           ∘ ε₂ ▻ l ▻ r₁
           ∘ assoc_inv _ _ _ ∘ assoc_inv _ _ _.
  Proof.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite assoc_natural.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ z))) (vcomp_assoc _ _ _)^).
    rewrite assoc_left, vcomp_left_identity.
    rewrite <- !vcomp_assoc.
    refine (vcomp_move_L_pM _ _ _ _) ; simpl.
    rewrite <- left_unit_natural.
    rewrite !vcomp_assoc.
    rewrite hcomp_id₂.
    rewrite <- interchange.
    rewrite !vcomp_left_identity, vcomp_right_identity.
    rewrite bc_whisker_l_compose.
    rewrite !vcomp_assoc.
    rewrite <- assoc_natural.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- right_unit_assoc.
    rewrite <- !vcomp_assoc.
    rewrite <- right_unit_natural.
    rewrite !vcomp_assoc.
    rewrite <- interchange.
    rewrite hcomp_id₂, !vcomp_left_identity, vcomp_right_identity.
    rewrite right_unit_id_is_left_unit_id.
    reflexivity.
  Qed.

  Definition remove_ε₁
    : ε₁ ∘ left_unit (l · r₁)
         ∘ assoc (id₁ Y) l r₁
         ∘ (ε₂ ▻ l ∘ assoc_inv l r₂ l ∘ l ◅ η₂ ∘ right_unit_inv l) ▻ r₁
      = ε₁.
  Proof.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- left_unit_assoc.
    rewrite !vcomp_assoc.
    rewrite <- bc_whisker_r_compose.
    refine (_ @ vcomp_right_identity _).
    f_ap.
    rewrite <- !vcomp_assoc.
    rewrite unit_counit_r.
    apply hcomp_id₂.
  Qed.

  Definition transport_counit
    : ε₂ ∘ l ◅ r₁_to_r₂ = ε₁.
  Proof.
    rewrite <- remove_ε₁.
    unfold r₁_to_r₂.
    do 3 rewrite bc_whisker_l_compose.
    rewrite <- !vcomp_assoc.
    rewrite help_triangle_ε.
    rewrite !vcomp_assoc.
    rewrite !bc_whisker_r_compose.
    repeat f_ap.
    refine (vcomp_move_L_Mp _ _ _ _) ; simpl.
    rewrite (ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite inverse_pentagon.
    rewrite <- !vcomp_assoc.
    rewrite <- !bc_whisker_r_compose.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite assoc_left, hcomp_id₂, vcomp_left_identity.
    rewrite !vcomp_assoc.
    rewrite (ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- bc_whisker_l_compose.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite assoc_right, hcomp_id₂, vcomp_left_identity.
    rewrite <- !vcomp_assoc.
    rewrite assoc_inv_natural.
    rewrite !vcomp_assoc.
    rewrite <- (vcomp_left_identity (id₂ r₁)).
    rewrite interchange, vcomp_left_identity.
    rewrite triangle_r_inv.
    reflexivity.
  Qed.

  Definition unique_adjoint
             `{LocallyUnivalent C}
    : A₁ = A₂.
  Proof.
    simple refine (path_sigma_hprop _ _ _).
    simple refine (path_sigma _ _ _ _ _) ; simpl.
    - refine (isotoid _ _ _ _).
      refine (@Build_Isomorphic _ _ _ r₁_to_r₂ _).
    - rewrite transport_prod ; simpl.
      apply path_prod'.
      + rewrite transport_two_cell_FlFr.
        rewrite ap_const ; simpl.
        rewrite <- transport_vcomp₁_r ; simpl.
        rewrite !vcomp_right_identity.
        rewrite eisretr ; cbn.
        apply transport_unit.
      + rewrite transport_two_cell_FlFr.
        rewrite ap_const.
        rewrite !vcomp_left_identity.
        refine (vcomp_move_R_pM _ _ _ _) ; simpl.
        rewrite <- transport_vcomp₁_l.
        rewrite eisretr ; cbn.
        symmetry.
        apply transport_counit.
  Defined.
End UniquenessAdjoint.

Global Instance ishprop_is_left_adjoint
       `{Funext}
       {C : BiCategory}
       `{LocallyUnivalent C}
       {X Y : C}
       (l : C⟦X,Y⟧)
  : IsHProp (is_left_adjoint l).
Proof.
  apply hprop_allpath.
  intros.
  apply unique_adjoint.
  assumption.
Defined.

Global Instance ishprop_is_adjoint_equivalence
       `{Funext}
       {C : BiCategory}
       `{LocallyUnivalent C}
       {X Y : C}
       (l : C⟦X,Y⟧)
  : IsHProp (is_adjoint_equivalence l).
Proof.
  apply hprop_allpath.
  intros.
  apply path_sigma_hprop.
  apply ishprop_is_left_adjoint.
Defined.

Definition path_adjoint_equivalence
           `{Funext}
           {C : BiCategory}
           `{LocallyUnivalent C}
           {X Y : C}
           {l₁ l₂ : X ≃ Y}
           (Hp : adjoint_equivalence_map l₁ = adjoint_equivalence_map l₂)
  : l₁ = l₂
  := path_sigma_hprop _ _ Hp.