import Pythia.LanguageSemantics.Palamedes.Gen

open Lean Elab Command Term Meta Gen

def optimizeBind? (x f : Expr) : MetaM (Option Expr) :=
  match_expr x with
  -- pure_bind : pure a >>= f ~~> f a
  | pure _ _ _ a => return some (.app f a)
  -- bind_bind : (x >>= f) >>= g ~~> x >>= (fun x -> f x >>= g)
  | bind _ _ _ _ x' g => do
    let .forallE _ argTy _ _ ← inferType g | return none
    let f' ← withLocalDecl `a .default argTy fun a => do
      mkLambdaFVars #[a] (← mkAppM ``bind #[.app g a, f])
    mkAppM ``bind #[x', f']
  -- assume_bind : assume b g >>= f ~~> assume b (fun h => g h >>= f)
  | assume _ b g => do
    let f' ← withLocalDecl `h .default (← mkEq b (.const ``true [])) fun h => do
      mkLambdaFVars #[h] (← mkAppM ``bind #[.app g h, f])
    mkAppM ``assume #[b, f']

  -- NOTE: These three rules are not strictly necessary, and could cause problems. If something goes
  -- wrong in optimization, try commenting these out.
  | pick _ x y => do
    if x.getUsedConstants.contains ``pick || y.getUsedConstants.contains ``pick then
      -- If `x` or `y` has a pick inside it, don't do this; we don't want exponential blowup
      -- TODO: This is kind of a hack. I'd love to come up with a more robust heuristic here at some
      -- point.
      return none
    mkAppM ``pick #[← mkAppM ``bind #[x, f], ← mkAppM ``bind #[y, f]]
  | dite _ P _ trueCase falseCase => do
    if trueCase.getUsedConstants.contains ``dite ||
       falseCase.getUsedConstants.contains ``dite ||
       trueCase.getUsedConstants.contains ``ite ||
       falseCase.getUsedConstants.contains ``ite
       then
      -- Same as above; rule out both `ite` and `dite`.
      return none
    let trueCase' ← withLocalDecl `h .default P fun h => do
      mkLambdaFVars #[h] (← mkAppM ``bind #[.app trueCase h, f])
    let falseCase' ← withLocalDecl `h .default (.app (.const ``Not []) P) fun h => do
      mkLambdaFVars #[h] (← mkAppM ``bind #[.app falseCase h, f])
    mkAppM ``dite #[P, trueCase', falseCase']
  | ite _ P _ trueCase falseCase => do
    if trueCase.getUsedConstants.contains ``dite ||
       falseCase.getUsedConstants.contains ``dite ||
       trueCase.getUsedConstants.contains ``ite ||
       falseCase.getUsedConstants.contains ``ite
       then
      -- Same as above; rule out both `ite` and `dite`.
      return none
    mkAppM ``ite #[P, ← mkAppM ``bind #[trueCase, f], ← mkAppM ``bind #[falseCase, f]]

  | _ => do
    lambdaBoundedTelescope f 1 fun args body => do
      -- bind_assume : x >>= fun a => assume b g ~~> assume b (fun h => (x >>= fun a => g h))
      --               (where a is not free in b)
      let #[a] := args | return none
      let_expr assume _ b g := body | return none

      -- NOTE: This check ensures that we're allowed to lift `b` out of the lambda that binds `a`,
      -- but it doesn't always behave as expected. In particular, if `b` has metavariables that
      -- might depend on `a`, this will fail. I wonder if we could detect if `b` MUST depend on `a`,
      -- and otherwise just assert that it doesn't and try pulling it out, but that might not be
      -- sound.
      if b.containsFVar a.fvarId! then return none

      let f' ← withLocalDecl `h .default (← mkEq b (.const ``true [])) fun h => do
        mkLambdaFVars #[h] (← mkAppM ``bind #[x, ← mkLambdaFVars #[a] (.app g h)])
      return some (← mkAppM ``assume #[b, f'])

def optimizePick? (x y : Expr) : MetaM (Option Expr) :=
  match_expr x with
  | assume _ b f =>
    match_expr y with
    | assume _ b' g =>
      -- if both x and y are `assume`s, then we have one of two cases:
      -- if they assume the same boolean:
        -- assume_pick : pick (assume b f) (assume b g) ~~> assume b (pick f g)
      if b == b' then do
        let c ← mkEq b (.const ``true [])
        let f' ← withLocalDecl `h .default c fun h => do
          mkLambdaFVars #[h] (← mkAppM ``pick #[.app f h, .app g h])
        return (some (← mkAppM ``assume #[b, f']))
      -- otherwise they assume different booleans:
        -- assume_pick : pick (assume b f) y ~~> if h : b then pick (f h) y else y
      else do
        let c ← mkEq b (.const ``true [])
        let fPos ← withLocalDecl `h .default c fun h => do
          mkLambdaFVars #[h] (← mkAppM ``pick #[.app f h, y])
        let fNeg ← withLocalDecl `h .default (.app (.const ``Not []) c) fun h =>
          mkLambdaFVars #[h] y
        return (some (← mkAppM ``dite #[c, fPos, fNeg]))
    -- if only x is an `assume`:
      -- assume_pick : pick (assume b f) y ~~> if h : b then pick (f h) y else y
    | _ => do
      let c ← mkEq b (.const ``true [])
      let fPos ← withLocalDecl `h .default c fun h => do
        mkLambdaFVars #[h] (← mkAppM ``pick #[.app f h, y])
      let fNeg ← withLocalDecl `h .default (.app (.const ``Not []) c) fun h =>
        mkLambdaFVars #[h] y
      return (some (← mkAppM ``dite #[c, fPos, fNeg]))
  | _ =>
    match_expr y with
    -- if only y is an `assume`:
      -- pick_assume : pick x (assume b f) ~~> if h : b then pick x (f h) else x
    | assume _ b f => do
      let c ← mkEq b (.const ``true [])
      let fPos ← withLocalDecl `h .default c fun h => do
        mkLambdaFVars #[h] (← mkAppM ``pick #[x, .app f h])
      let fNeg ← withLocalDecl `h .default (.app (.const ``Not []) c) fun h =>
        mkLambdaFVars #[h] x
      return (some (← mkAppM ``dite #[c, fPos, fNeg]))
    | _ => return none

def optimizeGen (e : Expr) : MetaM Expr := do
  let post (e : Expr) : MetaM TransformStep := do
    match_expr ← withReducible (reduce e) with
    | bind _ _ _ _ x f =>
      if let some e' ← optimizeBind? x f then return .visit e' else return .continue
    | pick _ x y =>
      if let some e' ← optimizePick? x y then return .visit e' else return .continue
    | _ => return .continue
  transform (post := post) e
