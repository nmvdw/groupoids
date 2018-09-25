Require Import HoTT.
From GR.bicategories Require Export
     general_category
     bicategory.bicategory
     bicategory.adjoint.

Definition transport_one_cell_FlFr
           `{Funext}
           {C : BiCategory}
           {A : Type}
           (f g : A -> C)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (h : C⟦f a₁,g a₁⟧)
  : (transport (fun (z : A) => C⟦f z,g z⟧) p h)
      ==>
      id_to_adjequiv _ _ (ap g p) · h · id_to_adjequiv _ _ (ap f p^)
  := match p with
     | idpath => right_unit_inv _ ∘ left_unit_inv _
     end.

Definition transport_one_cell_FlFr_inv
           `{Funext}
           {C : BiCategory}
           {A : Type}
           (f g : A -> C)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (h : C⟦f a₁,g a₁⟧)
  : (id_to_adjequiv _ _ (ap g p) · h · id_to_adjequiv _ _ (ap f p^))
      ==>
      transport (fun (z : A) => C⟦f z,g z⟧) p h
  := match p with
     | idpath => left_unit _ ∘ right_unit _
     end.

Global Instance is_iso_transport_one_cell_FlFr
       `{Funext}
       {C : BiCategory}
       {A : Type}
       (f g : A -> C)
       {a₁ a₂ : A}
       (p : a₁ = a₂)
       (h : C⟦f a₁,g a₁⟧)
  : IsIsomorphism (transport_one_cell_FlFr f g p h).
Proof.
  simple refine (Build_IsIsomorphism_2cell _ _ _).
  - apply transport_one_cell_FlFr_inv.
  - induction p ; simpl.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite right_unit_left, vcomp_left_identity.
    apply left_unit_left.
  - induction p ; simpl.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite left_unit_right, vcomp_left_identity.
    apply right_unit_right.
Defined.

Definition transport_vcomp₁_l
           `{Funext}
           {C : BiCategory}
           {X Y Z : C}
           (g : C⟦Y,Z⟧)
           {f₁ f₂ : C⟦X,Y⟧}
           (q : f₁ = f₂)
  : g ◅ idtoiso (C⟦X,Y⟧) q = idtoiso _ (ap (hcomp1 g) q).
Proof.
  induction q ; cbn.
  apply hcomp_id₂.
Defined.

Definition transport_vcomp₁_r
           `{Funext}
           {C : BiCategory}
           {X Y Z : C}
           (g : C⟦X,Y⟧)
           {f₁ f₂ : C⟦Y,Z⟧}
           (q : f₁ = f₂)
  : idtoiso (C⟦Y,Z⟧) q ▻ g = idtoiso _ (ap (fun (f : C⟦Y,Z⟧) => f · g) q).
Proof.
  induction q ; cbn.
  apply hcomp_id₂.
Defined.

Definition transport_two_cell_FlFr
           `{Funext}
           {C : BiCategory}
           {A : Type}
           {X Y : C}
           (F G : A -> C⟦X,Y⟧)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (α : F a₁ ==> G a₁)
  : transport (fun (z : A) => F z ==> G z) p α
    =
    idtoiso (C⟦X,Y⟧) (ap G p) ∘ α ∘ (idtoiso (C⟦X,Y⟧) (ap F p))^-1.
Proof.
  induction p ; cbn.
  rewrite vcomp_left_identity, vcomp_right_identity.
  reflexivity.
Qed.