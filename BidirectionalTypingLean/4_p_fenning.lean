-- 1. 型と項の拡張
inductive Ty where
  | unit : Ty
  | arrow : Ty → Ty → Ty
  | sum : Ty → Ty → Ty -- 直和型 A + B
deriving BEq, DecidableEq, Repr -- (guard を使うため BEq も入れておくと安心です)

inductive Expr where
  | unit : Expr
  | var : String → Expr
  | lam : String → Expr → Expr
  | app : Expr → Expr → Expr
  | anno : Expr → Ty → Expr
  -- 以下が追加
  | inl : Expr → Expr
  | inr : Expr → Expr
  | case : Expr → String → Expr → String → Expr → Expr
  | letE : String → Expr → Expr → Expr

def Context := List (String × Ty)

mutual
-- 型合成 (Synthesis: e ⇒ A)
def synthesize (ctx : Context) : Expr → Option Ty
    | .unit => some .unit

    | .var x => ctx.findSome? (fun (n, ty) => if n == x then some ty else none)

    | .anno e ty => do
        check ctx e ty
        return ty

    | .app e1 e2 => do
        -- 矢印型であることを要求（違えば none で早期リターン）
        let .arrow a b ← synthesize ctx e1 | none
        check ctx e2 a
        return b

    -- 【Let式 の合成】
    | .letE x e1 e2 => do
        let a ← synthesize ctx e1
        -- e1 で合成した型 a を文脈に追加し、e2 を合成する
        synthesize ((x, a) :: ctx) e2

    | _ => none

-- 型検査 (Checking: e ⇐ A)
def check (ctx : Context) : Expr → Ty → Option Unit
    | .unit, .unit => some ()

    | .lam x body, .arrow a1 a2 =>
        check ((x, a1) :: ctx) body a2

    -- 【直和型の導入則】
    | .inl e, .sum a b => check ctx e a
    | .inr e, .sum a b => check ctx e b

    -- 【+Elim (Case式) の除去則】
    | .case e x1 e1 x2 e2, targetTyC => do
        -- e を合成し、直和型 (A1 + A2) であることを要求する
        let .sum a1 a2 ← synthesize ctx e | none

        -- 分岐1 を C (targetTyC) で検査（失敗したらここで終了）
        check ((x1, a1) :: ctx) e1 targetTyC

        -- 分岐2 を C で検査（失敗したらここで終了）
        check ((x2, a2) :: ctx) e2 targetTyC

        -- 両方とも無事に通過したら合格！
        return ()

    -- 【Let式の検査】
    | .letE x e1 e2, targetTy => do
        let a ← synthesize ctx e1
        check ((x, a) :: ctx) e2 targetTy

    -- 【方向転換 (Subsumption)】
    | e, targetTy => do
        let synthTy ← synthesize ctx e
        -- 合成された型と目標型が一致するかをゲートチェック
        guard (synthTy == targetTy)
end