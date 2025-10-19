
#check Nat
#check Eq.rec
set_option pp.proofs true
set_option linter.unusedVariables false

theorem t1.{u} : {A : Sort u} -> {a : A} -> a = a :=
  fun {A : Sort u} =>
    fun {a : A} =>
      @Eq.refl.{u} A a

theorem inv.{u} : {A : Sort u} -> {a b : A} -> a = b -> b = a :=
  fun {A : Sort u} =>
    fun {a b : A} =>
      let D : (a b : A) -> (a = b) -> Prop :=
        fun (a b : A) =>
          fun (p : a = b) =>
            b = a
      @Eq.rec.{0, u} A a (D a) (Eq.refl a) b

theorem conc.{u} : {A : Sort u} -> {a b c : A} -> (a = b) -> (b = c) -> (a = c) :=
  fun {A : Sort u} =>
    fun {a b c : A} =>
      let D : (b : A) -> a = b -> Prop :=
        fun (b : A) =>
          fun (p : a = b) =>
            (b = c) -> (a = c)

      let d : (a = c) -> (a = c) :=
        fun (p : a = c) =>
          p

      @Eq.rec.{0,u} A a D d b

theorem ru.{u} : {A : Sort u} -> {a b : A} -> (p : a = b) -> (conc p (Eq.refl b)) = p :=
  fun {A : Sort u} =>
    fun {a b : A} =>

      let D : (b : A) -> a = b -> Prop :=
        fun (b : A) =>
          fun (p : a = b) =>
            (conc p (Eq.refl b)) = p

      let d : (Eq.refl a) = (Eq.refl a) :=
        Eq.refl (Eq.refl a)

      @Eq.rec.{0, u} A a D d b

theorem conc_assoc.{u} : {A : Sort u} -> {a b c d : A} -> (p : a = b) -> (q : b = c) -> (r : c = d) -> conc p (conc q r) = conc (conc p q) r :=
  fun {A : Sort u} =>
    fun {a b c d : A} =>
      let D_3 : (d : A) -> (p : a = d) -> Prop :=
        fun (d : A) =>
          fun (r : a = d) =>
            conc (Eq.refl a) (conc (Eq.refl a) r) = conc (conc (Eq.refl a) (Eq.refl a)) r

      let d_3 : (Eq.refl a) = (Eq.refl a) :=
        Eq.refl (Eq.refl a)

      let D_2 : (c : A) -> (q : a = c) -> Prop :=
        fun (c : A) =>
          fun (q : a = c) =>
            (r : c = d) -> conc (Eq.refl a) (conc q r) = conc (conc (Eq.refl a) q) r

      let d_2 : (r : a = d) -> conc (Eq.refl a) (conc (Eq.refl a) r) = conc (conc (Eq.refl a) (Eq.refl a)) r :=
        @Eq.rec.{0,u} A a D_3 d_3 d

      let D_1 : (b : A) -> (p : a = b) -> Prop :=
        fun b : A =>
          fun p : a = b =>
            (q : b = c) -> (r : c = d) -> conc p (conc q r) = conc (conc p q) r

      let d_1 : (q : a = c) -> (r : c = d) -> conc (Eq.refl a) (conc q r) = conc (conc (Eq.refl a) q) r :=
        @Eq.rec.{0, u} A a D_2 d_2 c

      @Eq.rec.{0, u} A a D_1 d_1 b
