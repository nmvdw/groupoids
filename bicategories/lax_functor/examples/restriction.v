Require Import HoTT.
Require Import HoTT.Categories.Functor.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.full_sub
     lax_functor.lax_functor.

Section RestrictionFunctor.
  Context {C D : BiCategory}.
  Variable (F : LaxFunctor C D)
           (P : C -> hProp).
  
  Definition lax_restriction_d : LaxFunctor_d (full_sub C P) D.
  Proof.
    make_laxfunctor.
    - exact (fun X => Fobj F X.1).
    - intros ; simpl in *.
      exact (Fmor F X.1 Y.1).
    - intros X Y Z g f ; cbn in *.      
      exact (Fcomp₁ F g f).
    - intros ; simpl.
      exact (Fid F X.1).
  Defined.

  Definition is_lax_restriction : is_lax lax_restriction_d.
  Proof.
    make_is_lax ; intros ; apply F.
  Qed.

  Definition lax_restriction : LaxFunctor (full_sub C P) D
    := Build_LaxFunctor lax_restriction_d is_lax_restriction.

  Global Instance lax_id_functor_pseudo
         `{is_pseudo _ _ F}
    : is_pseudo lax_restriction.
  Proof.
    simple refine {| Fcomp_iso := _ |} ; intros ; cbn in * ; apply _.
  Defined.
End RestrictionFunctor.