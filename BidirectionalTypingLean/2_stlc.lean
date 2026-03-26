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
     -- | .anno e ty => if (check ctx e ty).isSome then some ty else none
    | .anno e ty => do
        check ctx e ty -- 失敗(none)ならここで自動的に return none される
        return ty -- 成功したら ty を返す (some ty になる)

    -- 【除去則 = 合成】 →E⇒
    | .app e1 e2 => do
        -- 1. e1 を合成し、結果が arrow 型なら a と b に分解。それ以外なら `none` を返す
        let .arrow a b ← synthesize ctx e1 | none

        -- 2. e2 を a で検査。失敗したらここで自動終了
        check ctx e2 a

        -- 3. 全て成功したら b を返す
        return b
    | .unit | .lam .. => none

-- 型検査 (Checking: e ⇐ A)
def check (ctx : Context) : Expr → Ty → Option Unit
    -- 【導入則 = 検査】 unitI⇐
    | .unit, .unit => some ()

    -- 【導入則 = 検査】 →I⇐
    | .lam x body, .arrow a1 a2 =>
        check ((x, a1) :: ctx) body a2

    -- 【方向転換】 Sub⇐
    -- 合成と検査の境界線。
    | e, targetTy => do
        -- 1. e から型を合成する (失敗した場合は自動的に none が返って終了)
        let synthTy ← synthesize ctx e

        -- 2. 合成された型 (synthTy) と目標型 (targetTy) が一致するか判定
        if synthTy == targetTy then
            return ()
        else
            none
end