Require Import HoTT.
From HoTT.Categories Require Export
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory.

Definition cancel_L
           {C : PreCategory}
           {X Y Z : C}
           {f g : morphism C X Y}
           (h : morphism C Y Z)
           `{IsIsomorphism _ _ _ h}
  : (h o f = h o g)%morphism -> f = g.
Proof.
  intros Hhf.
  refine ((left_identity _ _ _ _)^ @ _ @ left_identity _ _ _ _).
  rewrite <- (@left_inverse _ _ _ h _).
  rewrite !associativity.
  rewrite Hhf.
  reflexivity.
Defined.

Definition cancel_R
           {C : PreCategory}
           {X Y Z : C}
           {f g : morphism C Y Z}
           (h : morphism C X Y)
           `{IsIsomorphism _ _ _ h}
  : (g o h = f o h)%morphism -> f = g.
Proof.
  intros Hfh.
  refine ((right_identity _ _ _ _)^ @ _ @ right_identity _ _ _ _).
  rewrite <- (@right_inverse _ _ _ h _).
  rewrite <- !associativity.
  rewrite Hfh.
  reflexivity.
Defined.

Section laws.
  Context {C : BiCategory}.

  Open Scope bicategory_scope.
  
  Definition triangle_l
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : right_unit g * id₂ f ∘ assoc_inv g (id₁ Y) f = id₂ g * left_unit f.
  Proof.
    rewrite triangle_r.
    rewrite vcomp_assoc.
    rewrite assoc_left.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.

  Definition bc_whisker_l_compose
             {X Y Z : C}
             (f : C⟦X,Y⟧)
             {g₁ g₂ g₃ : C⟦Y,Z⟧}
             (p₁ : g₁ ==> g₂) (p₂ : g₂ ==> g₃)
    : (p₂ ∘ p₁) ◅ f = (p₂ ◅ f) ∘ (p₁ ◅ f).
  Proof.
    rewrite <- interchange.
    rewrite vcomp_left_identity.
    reflexivity.
  Qed.

  Definition bc_whisker_r_compose
             {X Y Z : C}
             {f₁ f₂ f₃ : C⟦X,Y⟧}
             (g : C⟦Y,Z⟧)
             (p₁ : f₁ ==> f₂) (p₂ : f₂ ==> f₃)
    : g ▻ (p₂ ∘ p₁) = (g ▻ p₂) ∘ (g ▻ p₁).
  Proof.
    rewrite <- interchange.
    rewrite vcomp_left_identity.
    reflexivity.
  Qed.

  Definition left_comp
             {X Y : C}
             {f g : C⟦X,Y⟧}
             (η₁ η₂ : f ==> g)
             (Hη : id₂ (id₁ Y) * η₁ = id₂ (id₁ Y) * η₂)
    : η₁ = η₂.
  Proof.
    refine ((vcomp_left_identity η₁)^ @ _ @ vcomp_left_identity η₂).
    rewrite <- !left_unit_left.
    rewrite !vcomp_assoc.
    rewrite (left_unit_inv_natural η₁), (left_unit_inv_natural η₂).
    rewrite Hη.
    reflexivity.
  Qed.

  Definition right_comp
             {X Y : C}
             {f g : C⟦X,Y⟧}
             (η₁ η₂ : f ==> g)
             (Hη : η₁ * id₂ (id₁ X) = η₂ * id₂ (id₁ X))
    : η₁ = η₂.
  Proof.
    refine ((vcomp_right_identity η₁)^ @ _ @ vcomp_right_identity η₂).
    rewrite <- !right_unit_left.
    rewrite <- !vcomp_assoc.
    rewrite <- (right_unit_natural η₁), <- (right_unit_natural η₂).
    rewrite Hη.
    reflexivity.
  Defined.
  
  Definition left_unit_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : (left_unit g) ◅ f = left_unit (g · f) ∘ assoc (id₁ Z) g f.
  Proof.
  Admitted.
  (*apply right_comp.
  refine (cancel_L (assoc (id_m Z,c_m(g,id_m Y),f)) _).
  pose cancel_R.
  refine (cancel_R _ _ _ _).
  Search Category.Core.compose.
  pose (@right_inverse _ _ _ (assoc (id_m Z,c_m(g,id_m Y),f)) _).
  
  refine ((left_identity _ _ _ _)^ @ _).
  
  etransitivity.
  {
    Set Printing All.
  refine (_ @ ap (fun z => z o _)%morphism
            (@right_inverse _ _ _ (assoc (id_m Z,c_m(g,id_m Y),f)) _)).

  apply right_comp.
  
  pose (assoc (id_m Z,c_m(g,id_m Y),f)).
  refine ((left_identity _ _ _ _)^ @ _).
  pose (@right_inverse (_ -> _) _ _ (@assoc _ C X Y Z Z) _) as p.
  rewrite <- p.
  
  pose (@assoc _ C Y Z Z Z (id_m Z,id_m Z,g)).
  
  
  
  pose (triangle_r C Y Z Z (id_m Z) g).
  pose (1 : morphism (Hom C Y Z) g g)%morphism.
  pose (ap (fun z => hcomp m z) p).
  pose (@hcomp _ C).
  unfold two_cell, one_cell in t.
  cbn in t.
  Print hcomp.
  
  pose (pentagon C _ _ _ _ _ (id_m Z) (id_m Z) g f) as pent.    
  pose (@assoc _ C X Y Z Z (id_m Z,c_m(g,id_m Y),f))%morphism.
  pose (@assoc _ C Y Z Z Z (id_m Z,id_m Z,g)).
  cbn in m, m0.

  refine ((right_identity _ _ _ _)^ @ _).

  pose (commutes (@assoc _ C X Y Z Z)
                 (id_m Z,c_m (g,id_m Y),f)
                 (id_m Z,g,f)
                 (1,un_r _ _ g,1)%morphism) as assoc_com.
  pose (@right_inverse (_ -> _) _ _ (@assoc _ C X Y Z Z) _) as p.
  pose (equiv_path_natural_transformation _ _ p (id_m Z,c_m (g,id_m Y),f)) as q.
  simpl in q.
  Set Printing All.
  rewrite <- q.
  simpl in q.
  rewrite <- q.
  cbn in p0.
  (id_m Z,c_m (g,id_m Y),f)).
  ).
  pose pentagon.
  cbn.*)
  
  Definition right_unit_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : right_unit (g · f) = g ▻ (right_unit f) ∘ assoc g f (id₁ X).
  Proof.
  Admitted.

  Definition left_unit_is_right_unit
             `{Univalence}
             (X : C)
    : right_unit (id₁ X) = left_unit (id₁ X).
  Proof.
    assert (((id₂ (id₁ X) * left_unit (id₁ X)) ∘ assoc (id₁ X) (id₁ X) (id₁ X))
            = (id₂ (id₁ X) * right_unit (id₁ X)) ∘ assoc (id₁ X) (id₁ X) (id₁ X))
      as H0.
    {
      rewrite <- triangle_r.
      rewrite <- right_unit_assoc.
      refine ((vcomp_left_identity _)^ @ _ @ vcomp_left_identity _).
      rewrite <- right_unit_right.
      rewrite !vcomp_assoc.
      apply ap.
      apply (right_unit_natural (right_unit (id₁ X))).
    }
    assert (id₂ (id₁ X) * left_unit (id₁ X) = id₂ (id₁ X) * right_unit (id₁ X)) as H1.
    {
      refine (_ @ vcomp_right_identity _).
      rewrite <- assoc_left.
      rewrite <- vcomp_assoc.
      rewrite <- inverse_of_assoc.
      apply Morphisms.iso_moveL_pV.
      apply H0.
    }
    apply left_comp.
    apply H1^.
  Qed.

  Definition left_unit_inv_is_right_unit_inv
             `{Univalence}
             (X : C)
    : left_unit_inv (id₁ X) = right_unit_inv (id₁ X).
  Proof.
    rewrite <- inverse_of_left_unit, <- inverse_of_right_unit.
    apply Morphisms.iso_moveR_V1 ; simpl
    rewrite <- left_unit_is_right_unit.
    symmetry.
    apply right_unit_left.
  Qed.
End laws.