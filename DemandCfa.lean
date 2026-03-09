abbrev Var := String

inductive Expr where
  | ref (x : Var)
  | lam (x : Var) (e : Expr)
  | app (e1 e2 : Expr)
  deriving Repr, BEq, Inhabited

inductive Context where
  | top
  | appFun (arg : Expr) (outer : Context)
  | appArg (func : Expr) (outer : Context)
  | lamBod (var : Var) (outer : Context)
  deriving Repr, BEq, Inhabited

abbrev Cursor := Context × Expr

mutual
inductive Eval : Cursor → Cursor → Prop where
  | eval_lam {E x e} :
    Eval (E, Expr.lam x e) (E, Expr.lam x e)
  | eval_app {E E₀ e₀ e₁ e x csr} :
    Eval (Context.appFun e₁ E, e₀) (E₀, Expr.lam x e) →
    Eval (Context.lamBod x E₀, e) csr →
    Eval (E, Expr.app e₀ e₁) csr
  | eval_ref {E E₀ E' x e e₀ e₁ csr} :
    PathRel (E, Expr.ref x) (Context.lamBod x E₀, e) →
    Trace (E₀, Expr.lam x e) (E', Expr.app e₀ e₁) →
    Eval (Context.appArg e₀ E', e₁) csr →
    Eval (E, Expr.ref x) csr

inductive Trace : Cursor → Cursor → Prop where
  | trace_fun {E e₀ e₁} :
    Trace (Context.appFun e₁ E, e₀) (E, Expr.app e₀ e₁)
  | trace_arg {E E₀ E_x e₀ e₁ e x csr} :
    Eval (Context.appFun e₁ E, e₀) (E₀, Expr.lam x e) →
    PathRel (Context.lamBod x E₀, e) (E_x, Expr.ref x) →
    Trace (E_x, Expr.ref x) csr →
    Trace (Context.appArg e₀ E, e₁) csr
  | trace_bod {E x e csr₀ csr} :
    Trace (E, Expr.lam x e) csr₀ →
    Trace csr₀ csr →
    Trace (Context.lamBod x E, e) csr

inductive PathRel : Cursor → Cursor → Prop where
  | base_ref {x E} : PathRel (E, Expr.ref x) (E, Expr.ref x)
  | base_lam {x E e} : PathRel (Context.lamBod x E, e) (Context.lamBod x E, e)
  | step_fun {e1 E e0 c} : PathRel (E, Expr.app e0 e1) c → PathRel (Context.appFun e1 E, e0) c
  | step_arg {e0 E e1 c} : PathRel (E, Expr.app e0 e1) c → PathRel (Context.appArg e0 E, e1) c
  | step_lam {x y E e c} : x ≠ y → PathRel (E, Expr.lam y e) c → PathRel (Context.lamBod y E, e) c
  | sym {c1 c2} : PathRel c1 c2 → PathRel c2 c1
end

def trace_target_is_app {csr1 csr2 : Cursor} (H : Trace csr1 csr2) :
  ∃ E e₀ e₁, csr2 = (E, Expr.app e₀ e₁) :=
  match H with
  | Trace.trace_fun (E:=E) (e₀:=e₀) (e₁:=e₁) => ⟨E, e₀, e₁, rfl⟩
  | Trace.trace_arg (csr:=csr) _ _ h => trace_target_is_app h
  | Trace.trace_bod (csr:=csr) _ h => trace_target_is_app h

mutual
  theorem eval_to_trace {csr1 csr2 : Cursor} (H : Eval csr1 csr2) :
    ∀ {csr}, Trace csr1 csr → Trace csr2 csr :=
    fun {_} Htr =>
      match H with
      | .eval_lam => Htr
      | .eval_app h1 h2 =>
        let h_tr1 := eval_to_trace h1 .trace_fun
        let h_tr_bod := Trace.trace_bod h_tr1 Htr
        eval_to_trace h2 h_tr_bod
      | .eval_ref hb ht he =>
        let h_eval_site := trace_to_eval_gen ht rfl .eval_lam
        let h_tr_arg := Trace.trace_arg h_eval_site (PathRel.sym hb) Htr
        eval_to_trace he h_tr_arg

  theorem trace_to_eval_gen {csr1 csr2 : Cursor} (H : Trace csr1 csr2) :
    ∀ {E e₀ e₁}, csr2 = (E, Expr.app e₀ e₁) →
    ∀ {E_v v}, Eval csr1 (E_v, v) → Eval (Context.appFun e₁ E, e₀) (E_v, v) :=
    fun {E_goal e₀_goal e₁_goal} heq_goal {E_v v} h_eval1 =>
      match H with
      | Trace.trace_fun (E:=E_f) (e₀:=e₀_f) (e₁:=e₁_f) => by
        injection heq_goal with heqE heqapp
        injection heqapp with heqe₀ heqe₁
        subst_vars
        exact h_eval1
      | Trace.trace_arg (E:=E_a) (E₀:=E₀_a) (e₀:=e₀_a) (e₁:=e₁_a) (x:=x_a) (e:=e_a) h_eval_a h_p h_tr => by
        let h_tr_f := eval_to_trace h_eval_a Trace.trace_fun
        let h_eval_ref := Eval.eval_ref (PathRel.sym h_p) h_tr_f h_eval1
        exact trace_to_eval_gen h_tr heq_goal h_eval_ref
      | Trace.trace_bod (E:=E_b) (x:=x_b) (e:=e_b) (csr₀:=csr₀) h_tr1 h_tr2 => by
        let ⟨E₀', e₀₀', e₀₁', heq_csr₀⟩ := trace_target_is_app h_tr1
        let h_eval_csr₀ := Eval.eval_app (trace_to_eval_gen h_tr1 heq_csr₀ .eval_lam) h_eval1
        exact trace_to_eval_gen h_tr2 heq_goal (heq_csr₀.symm ▸ h_eval_csr₀)
end

/-- Main theorem: Demand 0CFA Soundness -/
theorem demand_0cfa_soundness (E E₀ : Context) (e₀ e₁ e : Expr) (x : Var) :
  Eval (Context.appFun e₁ E, e₀) (E₀, Expr.lam x e) ↔
  Trace (E₀, Expr.lam x e) (E, Expr.app e₀ e₁) := by
  constructor
  · intro h
    exact eval_to_trace h Trace.trace_fun
  · intro h
    exact trace_to_eval_gen h rfl .eval_lam
