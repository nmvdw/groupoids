Require Import HoTT.
Require Import Categories.Category.
Require Import Categories.Functor.
Require Import Categories.NaturalTransformation.
Require Import Categories.FunctorCategory.
Require Import Categories.Cat.

Definition prod_assoc (C D E : PreCategory)
  : Functor (C * (D * E)) ((C * D) * E).
Proof.
  simple refine (Build_Functor (C * (D * E))
                               ((C * D) * E)
                               (fun X => ((fst X, fst(snd X)), snd(snd X)))
                               _ _ _).
  - refine (fun X Y f => ((_,_), _)) ; apply f.
  - reflexivity.
  - reflexivity.
Defined.

Definition assoc_prod (C D E : PreCategory)
  : Functor ((C * D) * E) (C * (D * E)).
Proof.
  simple refine (Build_Functor ((C * D) * E)
                               (C * (D * E))
                               _
                               _ _ _).
  - intros [[a b] c].
    exact (a,(b,c)).
  - refine (fun X Y f => (_,(_, _))) ; apply f.
  - reflexivity.
  - reflexivity.
Defined.

Definition const_functor
           {C D : PreCategory}
           (X : D)
  : Functor C D
  := Build_Functor C
                   D
                   (fun _ => X)
                   (fun _ _ _ => Category.identity X)
                   (fun _ _ _ _ _ => (left_identity _ _ _ _)^)
                   (fun _ => idpath).

Definition pair
           {C₁ D₁ C₂ D₂ : PreCategory}
           {F₁ F₂ : Functor C₁ C₂}
           {G₁ G₂ : Functor D₁ D₂}
           (af : NaturalTransformation F₁ F₂)
           (ag : NaturalTransformation G₁ G₂)
  : NaturalTransformation (F₁,G₁) (F₂,G₂).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - exact (fun X => (af (fst X),ag (snd X))).
  - exact (fun X Y f => path_prod' (commutes af _ _ _) (commutes ag _ _ _)).
Defined.

Definition pair_l
           {C₁ D₁ C₂ D₂ : PreCategory}
           {F₁ F₂ : Functor C₁ C₂}
           {G : Functor D₁ D₂}
           (af : NaturalTransformation F₁ F₂)
  : NaturalTransformation (F₁,G) (F₂,G)
  := pair af 1.

Definition pair_r
           {C₁ D₁ C₂ D₂ : PreCategory}
           {F : Functor C₁ C₂}
           {G₁ G₂ : Functor D₁ D₂}
           (ag : NaturalTransformation G₁ G₂)
  : NaturalTransformation (F,G₁) (F,G₂)
  := pair 1 ag.

Section BiCategory.
  Context `{Univalence}.

  Record BiCategory :=
    Build_BiCategory {
        Obj : Type ;
        Hom : Obj -> Obj -> PreCategory ;
        id_m : forall (x : Obj), Hom x x ;
        c_m : forall {x y z : Obj}, Functor (Category.prod (Hom y z) (Hom x y)) (Hom x z) ;
        un_l : forall (X Y : Obj),
            NaturalTransformation (@c_m X Y Y o (const_functor (id_m Y) * 1))
                                  1 ;
        un_l_iso : forall (X Y : Obj), @IsIsomorphism (Hom X Y -> Hom X Y) _ _ (un_l X Y) ;
        un_r : forall (X Y : Obj),
            NaturalTransformation (@c_m X X Y o (1 * const_functor (id_m X)))
                                  1 ;
        un_r_iso : forall (X Y : Obj), @IsIsomorphism (Hom X Y -> Hom X Y) _ _ (un_r X Y) ;
        assoc : forall (w x y z : Obj),
          NaturalTransformation
            ((c_m o (c_m, 1)))
            (c_m o (1, c_m) o (assoc_prod (Hom y z) (Hom x y) (Hom w x))) ;
        assoc_iso : forall (w x y z : Obj), @IsIsomorphism
                                              ((Hom y z * Hom x y) * Hom w x -> Hom w z)
                                              _
                                              _
                                              (assoc w x y z) ;
        triangle : (forall (x y z : Obj) (g : Hom y z) (f : Hom x y),
                       @morphism_of _
                                    _
                                    c_m
                                    (c_m (g,id_m y),f)
                                    (g,f)
                                    ((un_r y z) g, 1)
                       =
                       (@morphism_of _
                                     _
                                     c_m
                                     (g,c_m (id_m y,f))
                                     (g,f)
                                     (1,un_l x y f))
                         o
                         (assoc x y y z) (g, id_m y, f))%morphism ;
        pentagon : (forall (v w x y z : Obj)
                           (k : Hom y z) (h : Hom x y) (g : Hom w x) (f : Hom v w),
                       (assoc v x y z (k,h,c_m (g,f)))
                         o assoc v w x z (c_m (k, h), g, f)
                       = (@morphism_of _
                                       _
                                       (@c_m v y z)
                                       (k,c_m (c_m (h,g),f))
                                       (k,c_m (h,c_m (g,f)))
                                       (1,assoc v w x y (h,g,f)))
                           o (assoc v w y z (k,c_m (h,g),f))
                           o
                           (@morphism_of _
                                         _
                                         (@c_m v w z)
                                         (c_m (c_m (k,h),g),f)
                                         (c_m (k,c_m (h,g)),f)
                                         (assoc w x y z (k,h,g),1)))%morphism
      }.
           
  Definition oneto (X : Type) `{IsTrunc 1 X} : PreCategory
    := Core.groupoid_category X.

  Definition oneto_cat (X : Type) `{IsTrunc 1 X} (x y : X) : IsCategory (oneto (x = y)).
  Proof.
    intros p q ; cbn in *.
    simple refine (isequiv_adjointify _ _ _ _).
    - intros α.
      apply α.
    - intros α.
      apply path_isomorphic.
      destruct α as [α αiso].
      induction α ; cbn in *.
      reflexivity.
    - intros r ; induction r.
      reflexivity.
  Defined.

  Definition concat_functor
             {X : Type} `{IsTrunc 2 X}
             (x y z : X)
    : Functor (oneto (y = z) * oneto (x = y)) (oneto (x = z)).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - exact (fun p => snd p @ fst p).
    - intros [p₁ p₂] [q₁ q₂] [r₁ r₂] ; cbn in *.
      induction r₁, r₂ ; reflexivity.
    - intros [p₁ p₂] [q₁ q₂] [r₁ r₂] [s₁ s₂] [t₁ t₂] ; cbn in *.
      induction s₁, t₁, s₂, t₂ ; reflexivity.
    - intros [p₁ p₂] ; reflexivity.
  Defined.

  Definition pUnitor_l
             {X : Type} `{IsTrunc 2 X}
             (x y : X)
    : @NaturalTransformation
        (oneto (x = y))
        (oneto (x = y))
        (concat_functor x y y o (@const_functor (oneto (x = y)) (oneto (y = y)) idpath * 1))
        (Functor.identity (oneto (x = y))).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + exact concat_p1.
    + intros ? ? p ; induction p.
      refine (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Definition pUnitor_l_inv
             {X : Type} `{IsTrunc 2 X}
             (x y : X)
    : @NaturalTransformation
        (oneto (x = y))
        (oneto (x = y))
        (Functor.identity (oneto (x = y)))
        (concat_functor x y y o (@const_functor (oneto (x = y)) (oneto (y = y)) idpath * 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + exact (fun p => (concat_p1 p)^).
    + intros ? ? p ; induction p.
      refine (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Global Instance pUnitor_l_iso {X : Type} `{IsTrunc 2 X} (x y : X)
    : @IsIsomorphism (oneto (x = y) -> oneto (x = y)) _ _ (pUnitor_l x y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply pUnitor_l_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      induction p ; reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      induction p ; reflexivity.
  Defined.
  
  Definition pUnitor_r
             {X : Type} `{IsTrunc 2 X}
             (x y : X)
    : @NaturalTransformation
        (oneto (x = y))
        (oneto (x = y))
        (concat_functor x x y o (1 * @const_functor (oneto (x = y)) (oneto (x = x)) idpath))
        (Functor.identity (oneto (x = y))).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + exact (fun p => concat_1p p).
    + intros ? ? p ; induction p ; cbn.
      refine (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Definition pUnitor_r_inv
             {X : Type} `{IsTrunc 2 X}
             (x y : X)
    : @NaturalTransformation
        (oneto (x = y))
        (oneto (x = y))
        (Functor.identity (oneto (x = y)))
        (concat_functor x x y o (1 * @const_functor (oneto (x = y)) (oneto (x = x)) idpath)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + exact (fun p => (concat_1p p)^).
    + intros ? ? p ; induction p.
      refine (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Global Instance pUnitor_r_iso {X : Type} `{IsTrunc 2 X} (x y : X)
    : @IsIsomorphism (oneto (x = y) -> oneto (x = y)) _ _ (pUnitor_r x y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply pUnitor_r_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      induction p ; reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      induction p ; reflexivity.
  Defined.

  Definition pAssociator
             {X : Type} `{IsTrunc 2 X}
             (w x y z : X)
    : NaturalTransformation
        (concat_functor w x z o (concat_functor x y z, 1))
        (concat_functor w y z o (1, concat_functor w x y)
                        o assoc_prod (oneto (y = z)) (oneto (x = y)) (oneto (w = x))).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[p₁ p₂] p₃] ; cbn in *.
      apply concat_p_pp.
    + intros [[p₁ p₂] p₃] [[q₁ q₂] q₃] [[r₁ r₂] r₃] ; cbn in *.
      induction p₁, p₂, p₃ ; cbn.
      rewrite <- r₁, <- r₂, <- r₃ ; cbn.
      reflexivity.
  Defined.

  Definition pAssociator_inv
             {X : Type} `{IsTrunc 2 X}
             (w x y z : X)
    : NaturalTransformation
        (concat_functor w y z o (1, concat_functor w x y)
                        o assoc_prod (oneto (y = z)) (oneto (x = y)) (oneto (w = x)))
        (concat_functor w x z o (concat_functor x y z, 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + cbn ; intros [[p q] r].
      apply concat_pp_p.
    + intros [[p₁ p₂] p₃] [[q₁ q₂] q₃] [[r₁ r₂] r₃] ; cbn in *.
      induction p₁, p₂, p₃ ; cbn.
      rewrite <- r₁, <- r₂, <- r₃ ; cbn.
      reflexivity.
  Defined.

  Global Instance pAssociator_iso {X : Type} `{IsTrunc 2 X} (w x y z : X)
    : @IsIsomorphism ((oneto (y = z) * oneto (x = y)) * oneto (w = x)
                      -> oneto (w = z))
                     _ _ (pAssociator w x y z).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply pAssociator_inv.
    - cbn.
      apply path_natural_transformation.
      intros [[p₁ p₂] p₃] ; cbn in *.
      induction p₁, p₂, p₃ ; reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros [[p₁ p₂] p₃] ; cbn in *.
      induction p₁, p₂, p₃ ; reflexivity.
  Defined.
      
  Definition twoto (X : Type) `{IsTrunc 2 X} : BiCategory.
  Proof.
    simple refine {|Obj := X ;
             Hom := fun x y => oneto (x = y) ;
             id_m := fun _ => idpath ;
             c_m := concat_functor ;
             un_l := pUnitor_l ;
             un_r := pUnitor_r ;
             assoc := pAssociator|}.
    - intros x y z p q ; cbn in *.
      induction p, q ; cbn.
      reflexivity.
    - cbn ; intros v w x y z s r q p.
      induction p, q, r, s ; cbn.
      reflexivity.
  Defined.

  Definition maps (A B : 1 -Type) : PreCategory.
  Proof.
    simple refine (@Build_PreCategory (A -> B) (fun f g => f = g) _ _ _ _ _ _).
    - reflexivity.
    - intros ? ? ? p q ; exact (q @ p).
    - cbn ; intros.
      apply concat_p_pp.
    - cbn ; intros.
      apply concat_p1.
    - cbn ; intros.
      apply concat_1p.
  Defined.

  Definition maps_cat (A B : 1 -Type) : IsCategory (maps A B).
  Proof.
    intros f g ; cbn in *.
    simple refine (isequiv_adjointify _ _ _ _).
    - intros α.
      apply α.
    - intros α.
      apply path_isomorphic.
      destruct α as [α αiso].
      induction α ; cbn in *.
      reflexivity.
    - intros p ; induction p.
      reflexivity.
  Defined.

  Definition comp_functor
             (A B C : 1 -Type)
    : Functor (maps B C * maps A B) (maps A C).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - exact (fun f => (fst f) o (snd f)).
    - intros [f₁ f₂] [g₁ g₂] [h₁ h₂] ; cbn in *.
      induction h₁, h₂ ; cbn.
      reflexivity.
    - intros [f₁ f₂] [g₁ g₂] [h₁ h₂] [p₁ p₂] [q₁ q₂] ; cbn in *.
      induction p₁, p₂, q₁, q₂ ; cbn.
      reflexivity.
    - intros [f₁ f₂] ; cbn in *.
      reflexivity.
  Defined.

  Definition cUnitor_l
             (A B : 1 -Type)
    : @NaturalTransformation
        (maps A B)
        (maps A B)
        (comp_functor A B B o (@const_functor (maps A B) (maps B B) idmap * 1))
        (Functor.identity (maps A B)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + reflexivity.
    + cbn ; intros ? ? p.
      induction p.
      reflexivity.
  Defined.

  Definition cUnitor_l_inv
             (A B : 1 -Type)
    : @NaturalTransformation
        (maps A B)
        (maps A B)
        (Functor.identity (maps A B))
        (comp_functor A B B o (@const_functor (maps A B) (maps B B) idmap * 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + reflexivity.
    + intros ? ? p ; cbn.
      induction p.
      reflexivity.
  Defined.

  Global Instance cUnitor_l_iso (A B : 1 -Type)
    : @IsIsomorphism (maps A B -> maps A B) _ _ (cUnitor_l A B).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply cUnitor_l_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
  Defined.
  
  Definition cUnitor_r
             (A B : 1 -Type)
    : @NaturalTransformation
        (maps A B)
        (maps A B)
        (comp_functor A A B o (1 * @const_functor (maps A B) (maps A A) idmap))
        (Functor.identity (maps A B)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + reflexivity.
    + intros ? ? p ; induction p ; cbn.
      reflexivity.
  Defined.

  Definition cUnitor_r_inv
             (A B : 1 -Type)
    : @NaturalTransformation
        (maps A B)
        (maps A B)
        (Functor.identity (maps A B))
        (comp_functor A A B o (1 * @const_functor (maps A B) (maps A A) idmap)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + reflexivity.
    + intros ? ? p ; induction p ; cbn.
      reflexivity.
  Defined.

  Global Instance cUnitor_r_iso (A B : 1 -Type)
    : @IsIsomorphism (maps A B -> maps A B) _ _ (cUnitor_r A B).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply cUnitor_r_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
  Defined.
  
  Definition cAssociator
             (A B C D : 1 -Type)
    : NaturalTransformation
        (comp_functor A B D o (comp_functor B C D, 1))
        (comp_functor A C D o (1, comp_functor A B C)
                        o assoc_prod (maps C D) (maps B C) (maps A B)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[f₁ f₂] f₃] ; cbn in *.
      reflexivity.
    + intros [[f₁ f₂] f₃] [[g₁ g₂] g₃] [[h₁ h₂] h₃] ; cbn in *.
      induction h₁, h₂, h₃ ; cbn.
      reflexivity.
  Defined.

  Definition cAssociator_inv
             (A B C D : 1 -Type)
    : NaturalTransformation
        (comp_functor A C D o (1, comp_functor A B C)
                      o assoc_prod (maps C D) (maps B C) (maps A B))
        (comp_functor A B D o (comp_functor B C D, 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[f₁ f₂] f₃] ; cbn in *.
      reflexivity.
    + intros [[f₁ f₂] f₃] [[g₁ g₂] g₃] [[h₁ h₂] h₃] ; cbn in *.
      induction h₁, h₂, h₃ ; cbn.
      reflexivity.
  Defined.

  Global Instance cAssociator_iso (A B C D : 1 -Type)
    : @IsIsomorphism ((maps C D * maps B C) * maps A B
                      -> maps A D)
                     _ _ (cAssociator A B C D).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply cAssociator_inv.
    - cbn.
      apply path_natural_transformation.
      intros [[f₁ f₂] f₃] ; cbn in *.
      reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros [[f₁ f₂] f₃] ; cbn in *.
      reflexivity.
  Defined.
  
  Definition onetypebi : BiCategory.
  Proof.
    simple refine {|Obj := 1 -Type ;
                    Hom := maps ;
                    id_m := fun _ => idmap ;
                    c_m := comp_functor ;
                    un_l := cUnitor_l ;
                    un_r := cUnitor_r ;
                    assoc := cAssociator|}.
    - intros A B C g f ; cbn.
      reflexivity.
    - intros A B C D E k h g f ; cbn.
      reflexivity.
  Defined.

  Definition interchange
             (C : BiCategory)
             {X Y Z : Obj C}
             {p q r : Hom C X Y}
             {p' q' r' : Hom C Y Z}
             (h : morphism _ p q) (h' : morphism _ p' q')
             (k : morphism _ q r) (k' : morphism _ q' r')
    : Type.
  Proof.
    simple refine (_ = _).
    - exact (morphism _ (c_m C (p',p)) (c_m C (r',r))).
    - simple refine (Category.compose _ _).
      + exact (c_m C (q',q)).
      + apply c_m ; split ; cbn.
        * exact k'.
        * exact k.
      + apply c_m ; split ; cbn.
        * exact h'.
        * exact h.
    - apply c_m ; split ; cbn.
      + exact (Category.compose k' h').
      + exact (Category.compose k h).
  Defined.

  Definition indeed
             (C : BiCategory)
             {X Y Z : Obj C}
             {p q r : Hom C X Y}
             {p' q' r' : Hom C Y Z}
             (h : morphism _ p q) (h' : morphism _ p' q')
             (k : morphism _ q r) (k' : morphism _ q' r')
    : interchange C h h' k k'.
  Proof.
    unfold interchange ; cbn.
    rewrite <- composition_of.
    cbn.
    reflexivity.
  Defined.
End BiCategory.

Section Morphism.
  Context `{Univalence}.
  
  Record LaxFunctor (C D : BiCategory) :=
    {
      Fobj : Obj C -> Obj D ;
      Fmor : forall (X Y : Obj C), Functor (Hom C X Y) (Hom D (Fobj X) (Fobj Y)) ;
      Fcomp : forall (X Y Z : Obj C),
          NaturalTransformation
            (Functor.compose
               (@c_m _ D (Fobj X) (Fobj Y) (Fobj Z))
               (Functor.pair (Fmor Y Z) (Fmor X Y)))
            (Functor.compose (Fmor X Z) (@c_m _ C X Y Z));
      Fid : forall (X : Obj C), Core.morphism _ (id_m D (Fobj X)) (Fmor X X (id_m C X)) ;
      Fun_r : forall (X Y : Obj C) (f : Hom C X Y),
          un_r D (Fobj X) (Fobj Y) (Fmor X Y f)
          =
          ((morphism_of (Fmor X Y) (un_r C X Y f))
             o (Fcomp X X Y (f,id_m C X))
             o (@morphism_of _
                             _
                             (c_m D)
                             (object_of (Fmor X Y) f,id_m D (Fobj X))
                             (object_of (Fmor X Y) f,object_of (Fmor X X) (id_m C X))
                             (1,Fid X))
          )%morphism ;
      Fun_l : forall (X Y : Obj C) (f : Hom C X Y),
          un_l D (Fobj X) (Fobj Y) (Fmor X Y f)
          =
          ((morphism_of (Fmor X Y) (un_l C X Y f))
             o (Fcomp X Y Y (id_m C Y,f))
             o (@morphism_of _
                             _
                             (c_m D)
                             (id_m D (Fobj Y),object_of (Fmor X Y) f)
                             (object_of (Fmor Y Y) (id_m C Y),object_of (Fmor X Y) f)
                             (Fid Y,1))
          )%morphism ;
      Fassoc : forall (W X Y Z : Obj C) (h : Hom C Y Z) (g : Hom C X Y) (f : Hom C W X),
          ((Fcomp W Y Z (h,c_m C (g,f)))
             o
             (@morphism_of _
                           _
                           (c_m D)
                           (object_of (Fmor Y Z) h,
                            c_m D (object_of (Fmor X Y) g,object_of (Fmor W X) f))
                           (object_of (Fmor Y Z) h,
                            object_of (Fmor W Y) (c_m C (g,f)))
                           (1,Fcomp W X Y (g,f)))
             o
             (assoc D _ _ _ _
                    (object_of (Fmor Y Z) h,
                     object_of (Fmor X Y) g,
                     object_of (Fmor W X) f)))%morphism
          =
          ((morphism_of (Fmor W Z) (assoc C W X Y Z (h,g,f)))
            o
            Fcomp W X Z (c_m C (h,g),f)
            o
            (@morphism_of _
                         _
                         (c_m D)
                         (c_m D (object_of (Fmor Y Z) h,
                                 object_of (Fmor X Y) g),object_of (Fmor W X) f)
                               (object_of (Fmor X Z) (c_m C (h,g)),object_of (Fmor W X) f)
                               (Fcomp X Y Z (h,g),1))
        )%morphism
    }.

  Definition ap_func
             {X Y : Type}
             `{IsTrunc 2 X} `{IsTrunc 2 Y}
             (f : X -> Y)
             {x₁ x₂ : X}
    : Functor (oneto (x₁ = x₂)) (oneto (f x₁ = f x₂)).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - cbn.
      exact (ap f).
    - cbn ; intros p q r.
      induction r.
      reflexivity.
    - cbn ; intros p q r s₁ s₂.
      induction s₁, s₂.
      reflexivity.
    - cbn ; intros p.
      reflexivity.
  Defined.

  Definition test
             {X Y : Type}
             `{IsTrunc 2 X} `{IsTrunc 2 Y}
             (f : X -> Y)
    : LaxFunctor (twoto X) (twoto Y).
  Proof.
    simple refine {| Fobj := _ |}.
    - cbn.
      exact f.
    - intros a b ; cbn.
      apply ap_func.
    - cbn.
      intros a b c.
      simple refine (Build_NaturalTransformation _ _ _ _).
      + cbn ; intros [p q].
        apply (ap_pp f q p)^.
      + intros [p₁ p₂] [q₁ q₂] [r₁ r₂] ; cbn in *.
        induction r₁, r₂ ; cbn.
        induction p₁, p₂ ; reflexivity.
    - intros a ; cbn.
      reflexivity.
    - intros a b p ; cbn in *.
      induction p ; cbn.
      reflexivity.
    - intros a b p ; cbn.
      induction p ; cbn.
      reflexivity.
    - intros a b c d p q r ; cbn.
      induction p, q, r ; cbn.
      reflexivity.
  Defined.
End Morphism.