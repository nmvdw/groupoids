Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.

Local Open Scope bicategory_scope.

Record LaxFunctor_d
       `{Univalence}
       (C D : BiCategory)
  := Build_LaxFunctor_d
       { Fobj_d :> Obj C -> Obj D ;
         Fmor_d : forall {X Y : C}, Functor (Hom C X Y) (Hom D (Fobj_d X) (Fobj_d Y)) ;
         Fcomp_d : forall {X Y Z : C},
             NaturalTransformation
               (c_m o (Functor.pair (@Fmor_d Y Z) (@Fmor_d X Y)))
               ((@Fmor_d X Z) o c_m);
         Fid_d : forall (X : C), morphism _ (id_m (Fobj_d X)) (Fmor_d (id_m X))
       }.

Arguments Build_LaxFunctor_d {_ C D} Fobj_d Fmor_d Fcomp_d Fid_d.
Arguments Fobj_d {_ C D}.
Arguments Fmor_d {_ C D} _ {X Y}.
Arguments Fcomp_d {_ C D} _ {X Y Z}.
Arguments Fid_d {_ C D}.

Definition path_LaxFunctor_d_help
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor_d C D}
           (obj_eq : Fobj_d F = Fobj_d G)
           (mor_eq : forall (X Y : C),
               transport (fun z => Functor (Hom C X Y) (Hom D z (G Y)))
                         (ap10 obj_eq X)
                         (transport (fun z => Functor (Hom C X Y) (Hom D _ z))
                                    (ap10 obj_eq Y)
                                    (@Fmor_d _ _ _ F X Y))
               =
               @Fmor_d _ _ _ G X Y)
  : Type.
Proof.
  simple refine ((forall (X : C), _ = Fid_d G X) *
                 (forall (X Y Z : C), _ = @Fcomp_d _ _ _ G X Y Z)).
  - induction (mor_eq X X).
    simpl in *.
    clear mor_eq.
    induction obj_eq ; simpl.
    exact (Fid_d F X).
  - induction (mor_eq X Z), (mor_eq Y Z), (mor_eq X Y) ; cbn in *.
    clear mor_eq.
    induction obj_eq ; simpl.
    exact (Fcomp_d F).
Defined.
  
Definition path_LaxFunctor_d
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor_d C D}
           (obj_eq : Fobj_d F = Fobj_d G)
           (mor_eq : forall (X Y : C),
              transport (fun z => Functor (Hom C X Y) (Hom D z (G Y)))
                          (ap10 obj_eq X)
                          (transport (fun z => Functor (Hom C X Y) (Hom D _ z))
                                     (ap10 obj_eq Y)
                                     (@Fmor_d _ _ _ F X Y))
              =
              @Fmor_d _ _ _ G X Y)
           (trans_eq : path_LaxFunctor_d_help obj_eq mor_eq)
  : F = G.
Proof.
  destruct trans_eq as [t1 t2].
  destruct F, G ; simpl in *.
  induction obj_eq ; simpl in *.
  pose (p := path_forall _ _ (fun x => path_forall _ _ (fun y => mor_eq x y))).
  assert (forall (X Y : C), mor_eq X Y = apD10 (apD10 p X) Y) as q.
  {
    intros ; unfold p.
    rewrite !apD10_path_forall.
    reflexivity.
  }
  induction p ; simpl in *.
  assert (Fid_d0 = Fid_d1) as X.
  {
    funext X.
    rewrite <- (t1 X), q ; cbn.
    reflexivity.
  }
  induction X.
  assert (Fcomp_d0 = Fcomp_d1) as X.
  {
    funext x y z.
    rewrite <- (t2 x y z), !q ; cbn.
    reflexivity.
  }
  induction X.
  reflexivity.
Defined.

Definition is_lax
           `{Univalence}
           {C D : BiCategory}
           (F : LaxFunctor_d C D)
  : hProp
  := BuildhProp
       ((forall {X Y : C} (f : Hom C X Y),
           un_r (Fobj_d F X) (Fobj_d F Y) (Fmor_d F f)
           =
           ((morphism_of (Fmor_d F) (un_r _ _ f))
              o (Fcomp_d F (f,id_m X))
              o (1 ∗ Fid_d F X))%morphism)
        *
        (forall (X Y : C) (f : Hom C X Y),
           un_l (Fobj_d F X) (Fobj_d F Y) (Fmor_d F f)
           =
           ((morphism_of (Fmor_d F) (un_l X Y f))
              o (Fcomp_d F (id_m Y,f))
              o (Fid_d F Y ∗ 1))%morphism)
        *
        (forall (W X Y Z : C) (h : Hom C Y Z) (g : Hom C X Y) (f : Hom C W X),
           ((Fcomp_d F (h, (g · f)))
              o (1 ∗ (Fcomp_d F (g,f)))
              o (assoc (Fmor_d F h,
                        Fmor_d F g,
                        Fmor_d F f))
           =
           (morphism_of (Fmor_d F) (assoc (h,g,f)))
             o Fcomp_d F (h · g,f)
             o (Fcomp_d F (h,g) ∗ 1))%morphism
       )).

Definition LaxFunctor `{Univalence} (C D : BiCategory)
  := {F : LaxFunctor_d C D & is_lax F}.

Definition Build_LaxFunctor
           `{Univalence}
           {C D : BiCategory}
           (F : LaxFunctor_d C D)
           (F_lax : is_lax F)
  : LaxFunctor C D
  := (F;F_lax).

Definition path_LaxFunctor
           `{Univalence}
           {C D : BiCategory}
           (F G : LaxFunctor C D)
           (Heq : F.1 = G.1)
  : F = G
  := path_sigma_hprop _ _ Heq.

Section LaxFunctorData.
  Context `{Univalence} {C D : BiCategory}.
  Variable (F : LaxFunctor C D).

  Definition Fobj : Obj C -> Obj D := Fobj_d F.1.

  Definition Fmor {X Y : C} : Functor (Hom C X Y) (Hom D (Fobj X) (Fobj Y))
    := Fmor_d F.1.

  Definition Fcomp {X Y Z : C}
    : NaturalTransformation
        (c_m o (Functor.pair (@Fmor Y Z) (@Fmor X Y)))
        ((@Fmor X Z) o c_m)
    := Fcomp_d F.1.

  Definition Fid (X : C)
    : morphism _ (id_m (Fobj X)) (Fmor (id_m X))
    := Fid_d F.1 X.

  Definition Fun_r {X Y : C} (f : Hom C X Y)
    : un_r (Fobj X) (Fobj Y) (Fmor f)
      =
      ((morphism_of Fmor (un_r _ _ f))
         o (Fcomp (f,id_m X))
         o (1 ∗ Fid X))%morphism.
  Proof.
    apply F.2.
  Defined.

  Definition Fun_l {X Y : C} (f : Hom C X Y)
    : un_l (Fobj X) (Fobj Y) (Fmor f)
      =
      ((morphism_of Fmor (un_l X Y f))
         o (Fcomp (id_m Y,f))
         o (Fid Y ∗ 1))%morphism.
  Proof.
    apply F.2.
  Defined.

  Definition Fassoc
             {W X Y Z : C}
             (h : Hom C Y Z) (g : Hom C X Y) (f : Hom C W X)
    : ((Fcomp (h, (g · f)))
         o (1 ∗ (Fcomp (g,f)))
         o (assoc (Fmor h,
                   Fmor g,
                   Fmor f))
       =
       (morphism_of Fmor (assoc (h,g,f)))
         o Fcomp (h · g,f)
         o (Fcomp (h,g) ∗ 1))%morphism.
  Proof.
    apply F.2.
  Defined.
End LaxFunctorData.

Coercion Fobj : LaxFunctor >-> Funclass.

Class is_pseudo_functor
      `{Univalence}
      {C D : BiCategory}
      (F : LaxFunctor C D)
  := { Fcomp_iso : forall {X Y Z : C},
         @IsIsomorphism (_ -> _)
                        _
                        _
                        (@Fcomp _ _ _ F X Y Z) ;
       Fid_iso : forall {X : C},
           IsIsomorphism (Fid F X)
     }.

Global Instance Fcomp_is_iso_class
       `{Univalence}
       {C D : BiCategory}
       (F : LaxFunctor C D)
       `{@is_pseudo_functor _ C D F}
       {X Y Z : C}
  : @IsIsomorphism (_ -> _) _ _ (@Fcomp _ _ _ F X Y Z).
Proof.
  apply Fcomp_iso.
Defined.

Global Instance Fid_is_iso_class
       `{Univalence}
       {C D : BiCategory}
       (F : LaxFunctor C D)
       `{@is_pseudo_functor _ _ _ F}
       {X : C}
  : IsIsomorphism (Fid F X).
Proof.
  apply Fid_iso.
Defined.