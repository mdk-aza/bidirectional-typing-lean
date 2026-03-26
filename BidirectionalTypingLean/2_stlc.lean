-- 型の定義: unit型 と 関数型(A -> B)
inductive Ty where
  | unit : Ty
  | arrow : Ty → Ty → Ty
deriving DecidableEq, Repr

-- 項の定義 [cite: 53]
inductive Expr where
  | unit : Expr -- ()
  | var : String → Expr -- 変数 x
  | lam : String → Expr → Expr -- ラムダ抽象 λx. e
  | app : Expr → Expr → Expr -- 関数適用 e1 e2
  | anno : Expr → Ty → Expr -- 型アノテーション (e : A)


-- 文脈は (変数名, 型) のリスト
def Context := List (String × Ty)

-- 文脈から変数を探す
def Context.lookup (ctx : Context) (name : String) : Option Ty :=
  ctx.findSome? (λ (n, ty) => if n == name then some ty else none)

  mutual

-- 型合成 (Synthesis: e ⇒ A)
def synthesize (ctx : Context) : Expr → Option Ty
    | .var x => ctx.findSome? (fun (n, ty) => if n == x then some ty else none)
    | .anno e ty => if (check ctx e ty).isSome then some ty else none

    -- 【除去則 = 合成】 →E⇒
    -- 関数 e1 が合成した型 (A → B) を分解し、引数 e2 の検査に A を再利用する
    | .app e1 e2 =>
        match synthesize ctx e1 with
        | some (.arrow a b) =>
            -- e2 を A で検査 (画像中央の青い矢印の流れ)
            match check ctx e2 a with
            | some _ => some b -- 結果として B を出力 (オレンジの矢印)
            | none => none
        | _ => none
    | .unit | .lam .. => none

-- 型検査 (Checking: e ⇐ A)
def check (ctx : Context) : Expr → Ty → Option Unit
    -- 【導入則 = 検査】 unitI⇐
    -- 目標型が unit であることが既知なので、即座に承認
    | .unit, .unit => some ()

    -- 【導入則 = 検査】 →I⇐
    -- 目標型 A1 → A2 が既知。文脈を (x : A1) で拡張し、body を A2 で検査
    | .lam x body, .arrow a1 a2 =>
        check ((x, a1) :: ctx) body a2

    -- 【方向転換】 Sub⇐
    -- 合成と検査の境界線。e から型 A を合成し、目標型 B と一致するか検証
    | e, targetTy =>
        match synthesize ctx e with
        | some synthTy =>
            -- A = B の検証 (画像右側の境界線)
            if synthTy == targetTy then some () else none
        | none => none
end