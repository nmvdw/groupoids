Require Import HoTT.
From GR.bicategories Require Import
     yoneda_lemma
     bicategory.bicategory
     lax_functor.lax_functor
     lax_functor.weak_equivalence
     lax_functor.examples.yoneda
     lax_functor.examples.image_restriction.

Definition rezk_completion
           `{Univalence}
           (C : BiCategory)
  : weak_equivalence (restrict_image (yoneda C)).
Proof.
  split.
  - refine (image_local_equivalence _ _).
    apply yoneda_local_equivalence.
  - apply image_essentialy_surjective.
Defined.