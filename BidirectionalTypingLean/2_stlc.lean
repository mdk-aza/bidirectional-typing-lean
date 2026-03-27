inductive Ty where
  | unit : Ty
  | arrow : Ty → Ty → Ty
deriving DecidableEq, Repr

inductive Expr where
  | unit : Expr -- ()
  | var : String → Expr -- 変数 x
  | lam : String → Expr → Expr -- ラムダ抽象 λx. e
  | app : Expr → Expr → Expr -- 関数適用 e1 e2
  | anno : Expr → Ty → Expr

-- 文脈は (変数名, 型) のリスト
def Context := List (String × Ty)

-- 文脈から変数を探す
def Context.lookup (ctx : Context) (name : String) : Option Ty :=
  ctx.findSome? (λ (n, ty) => if n == name then some ty else none)

  mutual

def synthesize (ctx : Context) : Expr → Option Ty
| .var x => ctx.lookup x
| .anno e ty =>
      match check ctx e ty with
      | none => none
      | some _ => some ty
  | .app e1 e2 =>
      match synthesize ctx e1 with
      | some (.arrow a b) =>
          match check ctx e2 a with
          | some _ => some b
          | none => none
      | _ => none
  | .unit | .lam .. => none

def check (ctx : Context) : Expr → Ty → Option Unit
| .unit, .unit => some ()
| .lam x body, .arrow a1 a2 => check ((x, a1) :: ctx) body a2
| e, targetTy =>
      match synthesize ctx e with
      | some synthTy => if synthTy == targetTy then some () else none
      | none => none

end

-- テスト1: 空の文脈で、() が unit型かチェックする
-- 期待される結果: some () （成功！）
#eval check [] Expr.unit Ty.unit

-- テスト2: 空の文脈で、() が (unit -> unit)型かチェックする
-- 期待される結果: none （型エラー！）
#eval check [] Expr.unit (Ty.arrow Ty.unit Ty.unit)

-- テスト3: 恒等関数 (λx. x) が (unit -> unit)型かチェックする
-- 期待される結果: some () （成功！）
#eval check [] (Expr.lam "x" (Expr.var "x")) (Ty.arrow Ty.unit Ty.unit)

-- テスト4: (λx. x) () という関数適用が unit型を合成するか？
-- 期待される結果: some Ty.unit
def idFunc := Expr.anno (Expr.lam "x" (Expr.var "x")) (Ty.arrow Ty.unit Ty.unit)
#eval synthesize [] (Expr.app idFunc Expr.unit)


-- 【1. 数学的な推論規則（仕様）の定義】
-- 合成（Synth: Γ ⊢ e ⇒ A）と 検査（Check: Γ ⊢ e ⇐ A）

mutual
-- 合成モードの規則 (Γ ⊢ e ⇒ A)
inductive Synth : Context → Expr → Ty → Prop where
    -- [Var⇒] 文脈から型が見つかれば、変数はその型を合成する
    | var_synth {ctx : Context} {x : String} {ty : Ty} :
        Context.lookup ctx x = some ty →
        Synth ctx (Expr.var x) ty

    -- [Anno⇒] アノテーションの中身が型Aとして検査をパスすれば、型Aを合成する
    | anno_synth {ctx : Context} {e : Expr} {ty : Ty} :
        Check ctx e ty →
        Synth ctx (Expr.anno e ty) ty

    -- [→E⇒] 関数適用 (e1 e2)
    | app_synth {ctx : Context} {e1 e2 : Expr} {a b : Ty} :
        Synth ctx e1 (Ty.arrow a b) → -- e1 が A → B を合成し
        Check ctx e2 a → -- e2 が A で検査できるなら
        Synth ctx (Expr.app e1 e2) b -- 全体は B を合成する

-- 検査モードの規則 (Γ ⊢ e ⇐ A)
inductive Check : Context → Expr → Ty → Prop where
    -- [UnitI⇐] () は unit型として検査できる
    | unit_check {ctx : Context} :
        Check ctx Expr.unit Ty.unit

    -- [→I⇐] ラムダ抽象 (λx. e) は A → B として検査できる
    | lam_check {ctx : Context} {x : String} {body : Expr} {a1 a2 : Ty} :
        Check ((x, a1) :: ctx) body a2 → -- x:A を文脈に追加して本体を B で検査
        Check ctx (Expr.lam x body) (Ty.arrow a1 a2)

    -- [Sub⇐] 方向転換: もし e が型 A を合成でき、かつ目標型も A なら、検査成功
    | sub_check {ctx : Context} {e : Expr} {ty : Ty} :
        Synth ctx e ty →
        Check ctx e ty
end


-- 【2. 健全性（Soundness）の定理】
-- 「プログラム（def）が計算で成功を返したら、数学的ルール（Prop）を満たす」という証明。
-- 項（Expr）の構造に関する帰納法で証明します。

theorem sizeOf_app_lt_left (e1 e2 : Expr) : sizeOf e1 < sizeOf (Expr.app e1 e2) := by
  simp [sizeOf, Expr._sizeOf_1]
  omega

theorem sizeOf_app_lt_right (e1 e2 : Expr) : sizeOf e2 < sizeOf (Expr.app e1 e2) := by
  simp [sizeOf, Expr._sizeOf_1]
  omega

  mutual
  -- 合成の健全性証明
theorem synthesize_sound {ctx : Context} {e : Expr} {ty : Ty}
    (h_eval : synthesize ctx e = some ty) : Synth ctx e ty := by
    cases h_e_eq : e with

    | unit =>
      rw [h_e_eq] at h_eval
      unfold synthesize at h_eval
      contradiction

    | var x =>
      rw [h_e_eq] at h_eval
      apply Synth.var_synth
      unfold synthesize at h_eval
      exact h_eval

    | lam x body =>
      rw [h_e_eq] at h_eval
      unfold synthesize at h_eval
      contradiction

    | app e1 e2 =>
      rw [h_e_eq] at h_eval
      revert h_eval
      unfold synthesize
      cases h_syn1 : synthesize ctx e1 with
      | none => simp_all
      | some ty1 =>
        cases ty1 with
        | unit => simp_all
        | arrow a b =>
          cases h_chk2 : check ctx e2 a with
          | none => simp_all
          | some _ =>
            simp_all
            intro h_eq_eval
            cases h_eq_eval
            apply Synth.app_synth
            · exact synthesize_sound h_syn1
            · exact check_sound h_chk2

    | anno e' ty' =>
      rw [h_e_eq] at h_eval
      revert h_eval
      unfold synthesize
      cases h_chk : check ctx e' ty' with
      | none => simp
      | some _ =>
        simp
        intro h_eq_eval
        cases h_eq_eval
        apply Synth.anno_synth
        exact check_sound h_chk

-- //
termination_by (sizeOf e, 0)
decreasing_by
all_goals simp_wf
·
    subst_vars
    left
    exact sizeOf_app_lt_left e1 e2
·
    subst_vars
    left
    exact sizeOf_app_lt_right e1 e2
·
    subst_vars
    left
    simp [sizeOf, Expr._sizeOf_1]
    omega


-- 検査の健全性証明
theorem check_sound {ctx : Context} {e : Expr} {ty : Ty}
    (h_eval : check ctx e ty = some ()) : Check ctx e ty := by
    cases h_e_eq : e with

    | unit =>
      rw [h_e_eq] at h_eval
      cases ty with
      | unit => exact Check.unit_check
      | arrow a b =>
        unfold check at h_eval
        simp_all [synthesize]

    | var x =>
      rw [h_e_eq] at h_eval
      unfold check at h_eval
      cases h_syn : synthesize ctx (Expr.var x) with
      | none => simp_all
      | some synthTy =>
        simp_all

        subst h_eval

        apply Check.sub_check
        exact synthesize_sound h_syn

    | lam x body =>
      rw [h_e_eq] at h_eval
      cases ty with
      | unit =>
        unfold check at h_eval
        simp_all [synthesize]
      | arrow a1 a2 =>
        apply Check.lam_check
        unfold check at h_eval
        exact check_sound h_eval

    | app e1 e2 =>
      rw [h_e_eq] at h_eval
      unfold check at h_eval
      cases h_syn : synthesize ctx (Expr.app e1 e2) with
      | none => simp_all
      | some synthTy =>
        simp_all
        subst h_eval
        apply Check.sub_check
        exact synthesize_sound h_syn

    | anno e' ty' =>
      rw [h_e_eq] at h_eval
      unfold check at h_eval
      cases h_syn : synthesize ctx (Expr.anno e' ty') with
      | none => simp_all
      | some synthTy =>
        simp_all
        subst h_eval
        apply Check.sub_check
        exact synthesize_sound h_syn

--
termination_by (sizeOf e, 1)
decreasing_by
all_goals simp_wf
all_goals subst_vars
all_goals (
    first
    | (apply Prod.Lex.left
       simp [sizeOf, Expr._sizeOf_1]
       omega)
    | (apply Prod.Lex.right
       omega))
end