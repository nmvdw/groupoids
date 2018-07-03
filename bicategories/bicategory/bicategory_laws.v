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
Admitted.

Definition cancel_R
           {C : PreCategory}
           {X Y Z : C}
           {f g : morphism C Y Z}
           (h : morphism C X Y)
           `{IsIsomorphism _ _ _ h}
  : (g o h = f o h)%morphism -> f = g.
Admitted.

Section laws.
  Context `{Univalence}
          {C : BiCategory}.
  
  Definition triangle_l
             {x y z : C}
             (g : Hom C y z) (f : Hom C x y)
    : (@morphism_of _
                    _
                    c_m
                    (c_m (g,id_m y),f)
                    (g,f)
                    ((un_r y z) g, 1)
                    o (assoc (g, id_m y, f))^-1
       =
       (@morphism_of _
                     _
                     c_m
                     (g,c_m (id_m y,f))
                     (g,f)
                     (1,un_l x y f)))%morphism.
  Proof.
    refine (ap (fun z => z o _) (triangle_r C x y z g f) @ _)%morphism.
    refine (associativity _ _ _ _ _ _ _ _ @ _).
    exact (ap (fun z => _ o z) right_inverse @ right_identity _ _ _ _)%morphism.
  Defined.

  Definition bc_whisker_l_compose
             {X Y Z : C}
             (f : one_cell X Y)
             {g₁ g₂ g₃ : one_cell Y Z}
             (p₁ : two_cell g₁ g₂) (p₂ : two_cell g₂ g₃)
    : (bc_whisker_l f _ (p₂ o p₁)
       =
       bc_whisker_l f _ p₂ o bc_whisker_l f _ p₁)%morphism.
  Proof.
    unfold bc_whisker_l.
    refine (_ @ composition_of _ _ _ _ _ _).
    apply ap ; cbn.
    apply (path_prod' idpath).
    exact (left_identity _ _ _ _)^.
  Defined.

  Definition bc_whisker_r_compose
             {X Y Z : C}
             {f₁ f₂ f₃ : one_cell X Y}
             (g : one_cell Y Z)
             (p₁ : two_cell f₁ f₂) (p₂ : two_cell f₂ f₃)
    : (bc_whisker_r _ g (p₂ o p₁)
       =
       bc_whisker_r _ g p₂ o bc_whisker_r _ g p₁)%morphism.
  Proof.
    unfold bc_whisker_r.
    refine (_ @ composition_of _ _ _ _ _ _).
    apply ap ; cbn.
    refine (path_prod' _ idpath).
    exact (left_identity _ _ _ _)^.
  Defined.

  Definition left_comp
             {X Y : C}
             {f g : Hom C X Y}
             (η₁ η₂ : two_cell f g)
             (Hη : (hcomp (1 : two_cell (id_m X) (id_m X)) η₁ = hcomp 1 η₂)%morphism)
    : η₁ = η₂.
  Proof.
    cbn in *.
    unfold hcomp in *.
    refine ((right_identity _ _ _ _)^ @ _ @ right_identity _ _ _ _).
    refine (ap (fun z => η₁ o z)%morphism (@right_inverse _ _ _ ((un_r X Y) f) _)^ @ _).
    refine (_ @ ap (fun z => η₂ o z)%morphism (@right_inverse _ _ _ ((un_r X Y) f) _)).
    rewrite <- !associativity.
    pose (commutes (un_r X Y) f g η₁) as p.
    cbn in p.
    rewrite <- p ; clear p.
    pose (commutes (un_r X Y) f g η₂) as p.
    cbn in p.
    rewrite <- p.
    repeat f_ap.
  Defined.

  Definition right_comp
             {X Y : C}
             {f g : Hom C X Y}
             (η₁ η₂ : two_cell f g)
             (Hη : (hcomp η₁ (1 : two_cell (id_m Y) (id_m Y)) = hcomp η₂ 1)%morphism)
    : η₁ = η₂.
  Proof.
    cbn in *.
    unfold hcomp in *.
    refine ((right_identity _ _ _ _)^ @ _ @ right_identity _ _ _ _).
    refine (ap (fun z => η₁ o z)%morphism (@right_inverse _ _ _ ((un_l X Y) f) _)^ @ _).
    refine (_ @ ap (fun z => η₂ o z)%morphism (@right_inverse _ _ _ ((un_l X Y) f) _)).
    rewrite <- !associativity.
    pose (commutes (un_l X Y) f g η₁) as p.
    cbn in p.
    rewrite <- p ; clear p.
    pose (commutes (un_l X Y) f g η₂) as p.
    cbn in p.
    rewrite <- p ; clear p.
    repeat f_ap.
  Defined.
  
  Definition un_l_assoc
             (X Y Z : C)
             (g : Hom C Y Z) (f : Hom C X Y)
    : @morphism_of _ _ c_m ((c_m (id_m Z, g)),f) (g,f) (un_l Y Z g,1%morphism)
      =
      (un_l X Z (c_m (g,f)) o assoc (id_m Z,g,f))%morphism.
  Proof.
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
  Admitted.

  Definition un_r_assoc
             (X Y Z : C)
             (g : Hom C Y Z) (f : Hom C X Y)
    : un_r X Z (c_m (g,f))
      =
      ((@morphism_of _ _ c_m (g,c_m (f,id_m X)) (g,f) (1,un_r X Y f))
         o
         assoc (g,f,id_m X))%morphism.
  Proof.
  Admitted.

  Definition un_l_is_un_r
             (X : C)
    : un_r X X (id_m X) = un_l X X (id_m X).
  Proof.
    assert ((@morphism_of _
                          _
                          c_m
                          (id_m X,c_m (id_m X,id_m X))
                          (id_m X,id_m X)
                          (1%morphism,un_l X X (id_m X)))
              o
              assoc (id_m X,id_m X, id_m X)
            =
            (@morphism_of _
                          _
                          c_m
                          (id_m X,c_m (id_m X,id_m X))
                          (id_m X,id_m X)
                          (1%morphism,un_r X X (id_m X)))
              o
              assoc (id_m X,id_m X, id_m X))%morphism as X0.
    {
      rewrite <- triangle_r.
      rewrite <- un_r_assoc.
      pose (commutes (un_r X X) (c_m (id_m X,id_m X)) (id_m X) (un_r X X (id_m X))).
      cbn in p.
      refine ((left_identity _ _ _ _)^ @ _ @ left_identity _ _ _ _).
      rewrite <- (@left_inverse _ _ _ (un_r X X (id_m X)) _).
      rewrite !associativity.
      apply ap.
      apply p.
    }
    assert ((@morphism_of _
                          _
                          c_m
                          (id_m X,c_m (id_m X,id_m X))
                          (id_m X,id_m X)
                          (1%morphism,un_l X X (id_m X)))
            =
            (@morphism_of _
                          _
                          c_m
                          (id_m X,c_m (id_m X,id_m X))
                          (id_m X,id_m X)
                          (1%morphism,un_r X X (id_m X)))) as X1.
    {
      refine (_ @ right_identity _ _ _ _).
      refine (_ @ ap (fun z => _ o z)%morphism
                (@right_inverse _ _ _ (assoc (id_m X, id_m X, id_m X)) _)).
      rewrite <- associativity.
      apply Morphisms.iso_moveL_pV.
      apply X0.
    }
    apply right_comp.
    apply X1^.
  Defined.

  Definition inv_un_l_is_inv_un_r (X : C)
    : (inverse (un_r X X) (id_m X) = inverse (un_l X X) (id_m X))%natural_transformation.
  Proof.
    apply Morphisms.iso_moveR_V1.
    rewrite un_l_is_un_r.
    rewrite right_inverse.
    reflexivity.
  Defined.
End laws.