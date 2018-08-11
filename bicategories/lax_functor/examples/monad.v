Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories.bicategory Require Import
     bicategory
     examples.terminal
     examples.precat
     examples.lax_functors_bicat.
From GR.bicategories.lax_functor Require Import
     lax_functor.
From GR.bicategories.lax_transformation Require Import
     lax_transformation.
From GR.bicategories.modification Require Import
     modification.

Section Monad.
  Context `{Univalence}.
  Variable (C : BiCategory).

  Definition monad := Lax terminal_bicategory C.

  Section MonadData.
    Variable (m : monad).
    
    Definition under_m :  C
      := Fobj m tt.

    Definition endo_m : C⟦under_m,under_m⟧
      := m ₁ tt.

    Definition unit : id₁ under_m ==> endo_m
      := Fid m tt.

    Definition bind : endo_m · endo_m ==> endo_m
      := Fcomp₁ m tt tt.

    Definition bind_unit
      : bind ∘ (unit ◅ endo_m) ∘ left_unit_inv endo_m
        =
        id₂ endo_m.
    Proof.
      unfold bind, unit, endo_m, bc_whisker_l ; cbn.
      rewrite <- left_unit_left.
      f_ap.
      rewrite left_unit_left.
      rewrite F_left_unit.      
      rewrite Fmor₂_id₂.
      rewrite vcomp_left_identity.
      reflexivity.
    Qed.

    Definition unit_bind
      : bind ∘ (endo_m ▻ unit) ∘ right_unit_inv endo_m
        =
        id₂ endo_m.
    Proof.
      unfold bind, unit, endo_m, bc_whisker_r ; cbn.
      rewrite <- right_unit_left.
      f_ap.
      rewrite right_unit_left.
      rewrite F_right_unit.
      rewrite Fmor₂_id₂.
      rewrite vcomp_left_identity.
      reflexivity.
    Qed.

    Definition bind_bind
      : bind ∘ (bind ◅ endo_m)
        =
        bind ∘ (endo_m ▻ bind) ∘ assoc endo_m endo_m endo_m.
    Proof.
      unfold bind, endo_m, bc_whisker_l, bc_whisker_r ; cbn.
      rewrite F_assoc.
      cbn.
      f_ap.
      rewrite Fmor₂_id₂.
      rewrite vcomp_left_identity.
      reflexivity.
    Qed.
  End MonadData.

  Definition monad_morphism (m₁ m₂ : monad)
    := monad⟦m₁,m₂⟧.

  Section MorphismData.
    Context {m₁ m₂ : monad}.
    Variable (η : monad_morphism m₁ m₂).

    Definition under_mm : C⟦under_m m₁,under_m m₂⟧
      := laxcomponent_of η tt.

    Definition under_mm_natural
      : endo_m m₂ · under_mm ==> under_mm · endo_m m₁
      := laxnaturality_of η tt.

    Definition under_mm_unit
      : under_mm_natural ∘ unit m₂ * id₂ under_mm
        =
        (id₂ under_mm * unit m₁ ∘ right_unit_inv under_mm) ∘ left_unit under_mm
      := transformation_unit η tt.

    Definition under_mm_bind
      : under_mm_natural ∘ bind m₂ * id₂ under_mm
        =
        (id₂ under_mm * bind m₁ ∘ assoc under_mm (endo_m m₁) (endo_m m₁))
          ∘ (under_mm_natural * id₂ (endo_m m₁))
          ∘ assoc_inv (endo_m m₂) under_mm (endo_m m₁)
          ∘ (id₂ (endo_m m₂) * under_mm_natural)
          ∘ assoc (endo_m m₂) (endo_m m₂) under_mm
      := transformation_assoc η tt tt.
  End MorphismData.

  Definition monad_transformation {m₁ m₂ : monad} (η₁ η₂ : monad_morphism m₁ m₂)
    := η₁ ==> η₂.

  Section TransformationData.
    Context {m₁ m₂ : monad}
            {η₁ η₂ : monad_morphism m₁ m₂}.
    Variable (σ : monad_transformation η₁ η₂).

    Definition under_mmm : under_mm η₁ ==> under_mm η₂
      := mod_component σ tt.

    Definition under_mmm_natural
      : under_mm_natural η₂ ∘ (endo_m m₂ ▻ under_mmm)
        =
        (under_mmm ◅ endo_m m₁) ∘ under_mm_natural η₁
      := mod_commute σ tt.
  End TransformationData.  
End Monad.