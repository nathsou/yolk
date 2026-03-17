
struct GlobalEnv {
  decls: Map[Name, Decl[Term]]
}

fn GlobalEnv::add(self: GlobalEnv, name: Name, decl: Decl[Term]) -> Unit raise TypeCheckError {
  if self.decls.contains(name) {
    raise DuplicateDeclaration(name)
  }

  self.decls[name] = decl
}

struct Context {
  mut next_free_var_id: FreeVarId 
  free_vars: Map[FreeVarId, Term]
  env: GlobalEnv
}

pub fn Context::new() -> Context {
  let ctx: Context = {
    env: { decls: {} },
    next_free_var_id: 0,
    free_vars: {},
  }

  ctx.init_default_inductives()
  ctx
}

pub fn Context::init_default_inductives(self: Context) -> Unit {
  let bool_ind: InductiveDecl[Term] = {
    params: [],
    constructors: [
      ("true", Const(Leaf("Bool"))),
      ("false", Const(Leaf("Bool"))),
    ],
    ty: Sort(1),
  }
  
  try! self.env.add(Leaf("Bool"), Inductive(bool_ind))

  try! self.env.add(Leaf("true"), Constructor(
    ind=bool_ind,
    ty=Const(Leaf("Bool")),
  ))

  try! self.env.add(Leaf("false"), Constructor(
    ind=bool_ind,
    ty=Const(Leaf("Bool")),
  ))

  let nat_ind: InductiveDecl[Term] = {
    params: [],
    constructors: [
      ("zero", Const(Leaf("Nat"))),
      ("succ", Pi(None, Const(Leaf("Nat")), Const(Leaf("Nat")))),
    ],
    ty: Sort(1),
  }
  
  try! self.env.add(Leaf("Nat"), Inductive(nat_ind))

  try! self.env.add(Path(Leaf("Nat"), "zero"), Constructor(
    ind=nat_ind,
    ty=Const(Leaf("Nat")),
  ))

  try! self.env.add(Path(Leaf("Nat"), "succ"), Constructor(
    ind=nat_ind,
    ty=Pi(None, Const(Leaf("Nat")), Const(Leaf("Nat"))),
  ))

  // Generate recursors for built-in inductive types
  try! self.generate_recursor(Leaf("Bool"), bool_ind)
  try! self.generate_recursor(Leaf("Nat"), nat_ind)
}

pub fn Context::add_decl(self: Context, name: Name, decl: Decl[Term]) -> Unit raise TypeCheckError {
  self.check_decl(name, decl)
  self.env.add(name, decl)
}

fn Context::check_decl(self: Context, name: Name, decl: Decl[Term]) -> Unit raise TypeCheckError {
  let ensure_sort = (decl_name: String, ty: Term) => {
    match self.whnf(self.infer(ty)) {
      Sort(u)  => u
      t => {
        raise TypeError(ty, "Invalid type for '\{decl_name}' '\{name}': expected a sort, got '\{t}'")
      }
    }
  }

  // check that all the top-level declarations are well-typed
  match decl {
    Axiom(ty) => { let _ = ensure_sort("axiom", ty) }
    Definition(ty, body) => {
      let _ = ensure_sort("definition", ty)
      self.check(body, ty)
    }
    Inductive({ ty, .. }) => {
      let arity_tys = ty.collect_pi_types()
      if !(arity_tys.last() is Some(Sort(_))) {
        raise TypeError(ty, "Invalid type for inductive '\{name}': expected a Pi type ending in a sort, got '\{ty}'")
      }
    }
    // https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#well-formed-inductives  
    // https://ammkrn.github.io/type_checking_in_lean4/declarations/inductive.html#constructor
    Constructor(ind={ params, ty: ind_ty, .. }, ty=ctor_ty) => {
      let inductive_name = Leaf(name.root())
      let _ = ensure_sort("constructor", ctor_ty)
      let free_vars_to_remove: Array[FreeVarId] = []
      
      defer {
        for var_id in free_vars_to_remove {
          self.free_vars.remove(var_id)
        }
      }

      // Open the inductive type's params to establish param FreeVars and get the opened arity
      let (param_vars, opened_arity) = self.open_binders(ind_ty, params.length(), free_vars_to_remove)
      let arity_tys = opened_arity.collect_pi_types()
      let ind_level = match arity_tys.last() {
        Some(Sort(u)) => u
        last => raise TypeError(ctor_ty, "Invalid constructor type for '\{name}': expected resulting type to be a sort, got '\{last}'")
      }

      // 1. Strip params from the constructor type, reusing the inductive type's param FreeVars
      let mut rem_ty = ctor_ty
      for i in 0..<param_vars.length() {
        match rem_ty {
          Pi(_, a, b) => {
            let { name: param_name, fvar: param_fvar, ty: param_ty } = param_vars[i]
            if !self.is_def_eq(a, param_ty) {
              raise TypeError(ctor_ty, "Constructor '\{name}' parameter type '\{a}' does not match inductive type '\{inductive_name}' parameter type '\{param_ty}'")
            }
            rem_ty = instantiate(b, 0, FreeVar(param_name, param_fvar))
          }
          _ => raise TypeError(ctor_ty, "Constructor '\{name}' has too few parameters compared to inductive type '\{inductive_name}'")
        }
      }

      // 2-4. Check non-parameter constructor arguments
      let mut arg_idx = 0
      while rem_ty is Pi(x, arg_ty, rest) {
        let s = self.infer(arg_ty)
        if self.whnf(s) is Sort(u) {
          if ind_level > 0 && u > ind_level {
            raise TypeError(
              ctor_ty,
              (
                #|Invalid universe level in constructor '\{name}':
                #|Parameter has type '\{arg_ty}' at universe level '\{u}' which is not less than or equal to the inductive type's resulting universe level '\{ind_level}'")
              )
            )
          }

          if !self.is_strictly_positive(arg_ty, inductive_name) {
            raise TypeError(ctor_ty, "Constructor '\{name}' has a non strictly-positive occurrence of the inductive type being declared in argument #\{arg_idx + 1}")
          }

          rem_ty = if x is Some(x) {
            let fresh_x = self.declare_fresh(arg_ty)
            free_vars_to_remove.push(fresh_x)
            open(rest, 0, x, fresh_x)
          } else {
            rest
          }
        } else {
          raise TypeError(ctor_ty, "Constructor '\{name}' has non-type parameter '\{arg_ty}'")
        }

        arg_idx += 1
      }

      // 5. Check return type is a valid application of the inductive type
      if !self.is_valid_inductive_app(rem_ty, inductive_name, param_vars, arity_tys) {
        raise TypeError(ctor_ty, "Constructor '\{name}' has invalid resulting type '\{rem_ty}', expected an application of the inductive type being declared to its parameters")
      }
    }
    Recursor(..) => {
      raise TypeError(decl.ty(), "Recursor '\{name}' cannot be declared manually; it is auto-generated")
    }
  }
}

// Given a term and an inductive name + param FreeVars, check if the term is
// an application of `I param_fvars... indices...`. If so, return Some(indices).
fn is_ind_app(term: Term, ind_name: Name, param_vars: Array[OpenedBinder]) -> ArrayView[Term]? {
  let (head, args) = term.collect_app_args()
  let n_params = param_vars.length()

  match head {
    Const(c) => {
      if c != ind_name || args.length() < n_params {
        return None
      }

      // Check that the first n_params args match the param FreeVars
      for i in 0..<n_params {
        let { name, fvar, .. } = param_vars[i]
        if !args[i].is_alpha_eq(FreeVar(name, fvar)) {
          return None
        }
      }

      Some(args[n_params:])
    }
    _ => None
  }
}

// Build a Term representing `I param_fvars... extra_args...`
fn mk_ind_app(ind_name: Name, param_vars: Array[OpenedBinder], extra_args: Array[Term]) -> Term {
  let mut result = Const(ind_name)

  for p in param_vars {
    result = App(result, FreeVar(p.name, p.fvar))
  }

  for a in extra_args {
    result = App(result, a)
  }

  result
}

// Build a term representing `f args...`
fn mk_app(f: Term, args: Iter[Term]) -> Term {
  let mut result = f

  for a in args {
    result = App(result, a)
  }

  result
}

// Close a single FreeVar and wrap in a Pi binder.
// If the variable doesn't occur in the body (non-dependent), use Pi(None, ...).
fn close_pi(body: Term, name: String, fvar_id: FreeVarId, fvar_ty: Term) -> Term {
  let closed_body = close(body, fvar_id, 0)
  if closed_body.has_loose_bvar(0) {
    Pi(Some(name), fvar_ty, closed_body)
  } else {
    Pi(None, fvar_ty, closed_body)
  }
}

/// Generate a recursor declaration for the given inductive type and add it to the environment.
fn Context::generate_recursor(self: Context, ind_name: Name, ind: InductiveDecl[Term]) -> Unit raise TypeCheckError {
  let { params, ty: ind_ty, constructors } = ind
  let num_params = params.length()
  let cleanup: Array[FreeVarId] = []

  defer {
    for var_id in cleanup {
      self.free_vars.remove(var_id)
    }
  }

  // 1. Open the parameter binders from the inductive type
  let (param_vars, opened_arity) = self.open_binders(ind_ty, num_params, cleanup)

  // 2. Open the index binders from the opened arity
  let mut remaining = opened_arity
  let index_vars: Array[OpenedBinder] = []
  let mut index_idx = 1

  while remaining is Pi(x, a, b) {
    let name = match x { Some(x) => x; None => "idx\{index_idx}" }
    let fresh = self.declare_fresh(a)
    cleanup.push(fresh)
    index_vars.push({ name, fvar: fresh, ty: a })
    remaining = instantiate(b, 0, FreeVar(name, fresh))
    index_idx += 1
  }

  let num_indices = index_vars.length()

  // 3. Get the result universe level
  let result_level: UniverseLevel = match remaining {
    Sort(u) => u
    _ => raise TypeError(ind_ty, "Inductive type '\{ind_name}' does not end in a Sort")
  }

  // 4. Build the target type: I param_fvars... index_fvars...
  let index_fvar_terms: Array[Term] = index_vars.map(b => FreeVar(b.name, b.fvar))
  let target_type = mk_ind_app(ind_name, param_vars, index_fvar_terms)

  // 5. Build the motive type: forall (indices...), forall (t : I params... indices...), Sort(result_level)
  let motive_target_var_id = self.declare_fresh(target_type)
  cleanup.push(motive_target_var_id)
  let mut motive_body = Term::Sort(result_level)
  let motive_target_name = "t"
  motive_body = close_pi(motive_body, motive_target_name, motive_target_var_id, target_type)

  for i = index_vars.length() - 1; i >= 0; i = i - 1 {
    let idx = index_vars[i]
    motive_body = close_pi(motive_body, idx.name, idx.fvar, idx.ty)
  }

  // Declare the motive FreeVar
  let motive_fvar_id = self.declare_fresh(motive_body)
  cleanup.push(motive_fvar_id)
  let motive_name = "motive"
  let motive_fvar = FreeVar(motive_name, motive_fvar_id)

  // 6. For each constructor, build its minor premise type
  let minor_vars: Array[OpenedBinder] = []
  let rec_rules: Array[RecRule] = []
  for ctor in constructors {
    let (ctor_name, ctor_ty) = ctor
    let minor_cleanup: Array[FreeVarId] = []
    defer {
      for var_id in minor_cleanup {
        self.free_vars.remove(var_id)
      }
    }

    // The constructor types from the Inductive decl have loose BoundVars
    // referring to params. Instantiate them with the param FreeVars.
    // BoundVar(i) refers to param_vars[num_params - 1 - i]
    let mut ctor_remaining = ctor_ty
    for i in 0..<num_params {
      let p = param_vars[num_params - 1 - i]
      ctor_remaining = instantiate(ctor_remaining, i.reinterpret_as_uint(), FreeVar(p.name, p.fvar))
    }

    // Collect constructor arguments (non-param args) by opening Pi binders
    let ctor_arg_vars: Array[OpenedBinder] = []
    let mut param_idx = 1
    while ctor_remaining is Pi(x, a, b) {
      let name = match x { Some(x) => x; None => "a\{param_idx}" }
      let fresh = self.declare_fresh(a)
      cleanup.push(fresh)
      minor_cleanup.push(fresh)
      ctor_arg_vars.push({ name, fvar: fresh, ty: a })
      ctor_remaining = instantiate(b, 0, FreeVar(name, fresh))
      param_idx += 1
    }

    // ctor_remaining is now the return type: I params... i1 ... im
    // Extract the constructor's specific indices
    let ctor_indices = match is_ind_app(ctor_remaining, ind_name, param_vars) {
      Some(idxs) => idxs
      None => raise TypeError(ctor_ty, "Constructor '\{ctor_name}' return type is not a valid application of '\{ind_name}'")
    }

    // Build the constructor application: ctor_full_name param_fvars... arg_fvars...
    // Resolve the full constructor name
    let ctor_full_name: Name = if self.env.decls.contains(Path(ind_name, ctor_name)) {
      Path(ind_name, ctor_name)
    } else {
      Leaf(ctor_name)
    }

    let mut ctor_app = Const(ctor_full_name)
    for p in param_vars {
      ctor_app = App(ctor_app, FreeVar(p.name, p.fvar))
    }

    for a in ctor_arg_vars {
      ctor_app = App(ctor_app, FreeVar(a.name, a.fvar))
    }

    // Build IH (inductive hypothesis) FreeVars for recursive arguments
    let ih_vars: Array[OpenedBinder] = []
    let rec_field_indices: Array[Int] = []
    for i, a in ctor_arg_vars {
      if is_ind_app(a.ty, ind_name, param_vars) is Some(rec_indices) {
        rec_field_indices.push(i)
        // IH type: C rec_indices... a_fvar
        let ih_ty = mk_app(motive_fvar, rec_indices.iter())
        let ih_ty = Term::App(ih_ty, FreeVar(a.name, a.fvar))
        let ih_name = "\{a.name}_ih"
        let ih_fvar = self.declare_fresh(ih_ty)
        cleanup.push(ih_fvar)
        minor_cleanup.push(ih_fvar)
        ih_vars.push({ name: ih_name, fvar: ih_fvar, ty: ih_ty })
      }
    }

    // Minor premise result: C ctor_indices... ctor_app
    let mut minor_result = mk_app(motive_fvar, ctor_indices.iter())
    minor_result = App(minor_result, ctor_app)

    // Close IH vars, then ctor_arg vars
    for i = ih_vars.length() - 1; i >= 0; i = i - 1 {
      let ih = ih_vars[i]
      minor_result = close_pi(minor_result, ih.name, ih.fvar, ih.ty)
    }

    for i = ctor_arg_vars.length() - 1; i >= 0; i = i - 1 {
      let a = ctor_arg_vars[i]
      minor_result = close_pi(minor_result, a.name, a.fvar, a.ty)
    }

    // Record the RecRule for this constructor
    rec_rules.push({ ctor: ctor_full_name, num_fields: ctor_arg_vars.length(), rec_fields: rec_field_indices })

    // Declare the minor premise FreeVar
    let minor_fvar = self.declare_fresh(minor_result)
    cleanup.push(minor_fvar)
    minor_vars.push({ name: ctor_name, fvar: minor_fvar, ty: minor_result })
  }

  // 7. Build the final recursor type
  // Result: C index_fvars... major
  let major_fvar_id = self.declare_fresh(target_type)
  cleanup.push(major_fvar_id)
  let major_fvar_name = "major"
  let major_fvar = FreeVar(major_fvar_name, major_fvar_id)

  let mut rec_result = mk_app(motive_fvar, index_fvar_terms.iter())
  rec_result = App(rec_result, major_fvar)

  // Close from inside out: major → indices → minors → motive → params
  rec_result = close_pi(rec_result, major_fvar_name, major_fvar_id, target_type)
  for i = index_vars.length() - 1; i >= 0; i = i - 1 {
    let idx = index_vars[i]
    rec_result = close_pi(rec_result, idx.name, idx.fvar, idx.ty)
  }

  for i = minor_vars.length() - 1; i >= 0; i = i - 1 {
    let m = minor_vars[i]
    rec_result = close_pi(rec_result, m.name, m.fvar, m.ty)
  }

  rec_result = close_pi(rec_result, motive_name, motive_fvar_id, motive_body)
  for i = param_vars.length() - 1; i >= 0; i = i - 1 {
    let p = param_vars[i]
    rec_result = close_pi(rec_result, p.name, p.fvar, p.ty)
  }

  // 8. Add to the environment
  self.env.add(Path(ind_name, "rec"), Recursor(
    ind~,
    ty=rec_result,
    num_params~,
    num_indices~,
    num_minors=constructors.length(),
    rules=rec_rules,
  ))
}

fn Context::is_strictly_positive(self: Context, ty: Term, inductive_type_name: Name) -> Bool raise TypeCheckError {
  // non-recursive case
  if !const_occurs_in(inductive_type_name, ty) {
    return true
  }

  match ty {
    Const(_) => true // `I`: simple case
    App(_) => { // `I t1, ..., tn` simple case, where I does not occur in ti for any i
      let (_head, args) = ty.collect_app_args()
      return !args.iter().any(arg => const_occurs_in(inductive_type_name, arg))
    }
    Pi(_, a, b) => { // functional case
      !const_occurs_in(inductive_type_name, a) && self.is_strictly_positive(b, inductive_type_name)
    }
    _ => true
  }
}

struct OpenedBinder {
  name: String
  fvar: FreeVarId
  ty: Term
}

// Opens `n` leading Pi binders of `ty`, replacing each bound variable with a fresh FreeVar.
fn Context::open_binders(
  self: Context,
  ty: Term,
  n: Int,
  cleanup: Array[FreeVarId]
) -> (Array[OpenedBinder], Term) raise TypeCheckError {
  let binders: Array[OpenedBinder] = []
  let mut remaining = ty

  for _ in 0..<n {
    match remaining {
      Pi(x, a, b) => {
        let name = match x { Some(x) => x; None => "_" }
        let fresh = self.declare_fresh(a)
        cleanup.push(fresh)
        binders.push({ name, fvar: fresh, ty: a })
        remaining = instantiate(b, 0, FreeVar(name, fresh))
      }
      _ => raise TypeError(ty, "Expected at least \{n} Pi binders")
    }
  }

  (binders, remaining)
}

// Checks that `term` is a valid return type for a constructor of `inductive_name`:
//   - head is `inductive_name`
//   - the first `param_vars.length()` arguments are exactly the parameter FreeVars (by value)
//   - the remaining arguments match the index types from the opened arity
fn Context::is_valid_inductive_app(
  self: Context,
  term: Term,
  inductive_name: Name,
  param_vars: Array[OpenedBinder],
  arity_tys: Array[Term]
) -> Bool raise TypeCheckError {
  let (head, args) = term.collect_app_args()
  let n_params = param_vars.length()
  let n_indices = arity_tys.length() - 1

  let head_ok = match head {
    Const(n) => n == inductive_name
    _ => false
  }

  if !head_ok || args.length() != n_params + n_indices {
    return false
  }

  for i in 0..<n_params {
    let { name, fvar, .. } = param_vars[i]
    if !self.is_def_eq(args[i], FreeVar(name, fvar)) {
      return false
    }
  }

  for i in 0..<n_indices {
    let index_ty = self.infer(args[n_params + i])
    if !self.is_def_eq(arity_tys[i], index_ty) {
      return false
    }
  }

  true
}

fn Context::fresh_var_id(self: Context) -> FreeVarId raise TypeCheckError {
  let id = self.next_free_var_id
  if id == @uint.max_value {
    raise FreeVarIdOverflow
  }

  self.next_free_var_id += 1
  id
}

fn Context::declare_fresh(self: Context, ty: Term) -> FreeVarId raise TypeCheckError {
  let var_id = self.fresh_var_id()
  self.free_vars[var_id] = ty
  var_id
}

fn Context::lookup_free_var(self: Context, var_id: FreeVarId) -> Term? {
  self.free_vars.get(var_id)
}

fn Context::normalise(self: Context, term: Term) -> Term raise TypeCheckError {
  match term {
    Const(name) => {
      if self.env.decls.get(name) is Some(decl) {
        match decl {
          Axiom(_) => term
          // delta reduction: unfold definitions
          Definition(_, body) => self.normalise(body)
          Inductive(_) => term
          Constructor(_) => term
          Recursor(_) => term
        }
      } else {
        Const(name)
      }
    }
    App(lhs, rhs) => {
      let lhs_norm = self.normalise(lhs)
      let rhs_norm = self.normalise(rhs)

      match lhs_norm {
        Lam(_, _, body) => self.normalise(instantiate(body, 0, rhs_norm))
        _ => {
          let result = Term::App(lhs_norm, rhs_norm)
          let (head, args) = result.collect_app_args()
          match self.try_iota_reduce(head, args) {
            Some(reduced) => self.normalise(reduced)
            None => result
          }
        }
      }
    }
    Lam(x, ty, body) => {
      // 1. Generate a fresh FreeVar
      let fresh_x = self.declare_fresh(ty)
      defer self.free_vars.remove(fresh_x)

      // 2. Open the binder, replacing BoundVar(0) with the FreeVar
      let opened = open(body, 0, x, fresh_x)

      // 3. Normalise the locally closed body
      let norm_body = self.normalise(opened)

      // 4. Close the FreeVar back into BoundVar(0)
      let closed = close(norm_body, fresh_x, 0)

      // 5. eta-conversion: (fun x => f x) <=> f, when x is not free in f
      if closed is App(f, BoundVar(0)) && !f.has_loose_bvar(0) {
        return f
      }

      Lam(x, self.normalise(ty), closed)
    }
    Pi(x, a, b) => {
      let a_norm = self.normalise(a)
      let b_norm = if x is Some(x) {
        let fresh_x = self.declare_fresh(a)
        defer self.free_vars.remove(fresh_x)

        let opened = open(b, 0, x, fresh_x)
        close(self.normalise(opened), fresh_x, 0)
      } else {
        self.normalise(b)
      }

      Pi(x, a_norm, b_norm)
    }
    Let(_, val, body) => self.normalise(instantiate(body, 0, self.normalise(val)))
    Ann(lhs, _) => self.normalise(lhs)
    Sort(_) | BoundVar(_) | FreeVar(_) => term
  }
}

// Extract indices from a term of the form `I params... idx1 ... idxN`
fn extract_indices(term: Term, ind_name: Name, num_params: Int) -> ArrayView[Term]? {
  let (head, args) = term.collect_app_args()

  if head is Const(c) && c == ind_name && args.length() >= num_params {
    Some(args[num_params:])
  } else {
    None
  }
}

// Try iota reduction: if head is a recursor and the major premise reduces to a constructor, fire the rule
fn Context::try_iota_reduce(self: Context, head: Term, args: ArrayView[Term]) -> Term? {
  let rec_name = if head is Const(name) { name } else { return None }
  let ind_name = Leaf(rec_name.root())
  let (ind, num_params, num_indices, num_minors, rules) = match self.env.decls.get(rec_name) {
    Some(Recursor(ind~, num_params~, num_indices~, num_minors~, rules~, ..)) =>
      (ind, num_params, num_indices, num_minors, rules)
    _ => return None
  }

  // Total expected args: params + motive + minors + indices + major
  let total_args = num_params + 1 + num_minors + num_indices + 1
  if args.length() < total_args {
    return None
  }

  // Decompose args
  let params = args[0:num_params]
  // motive at args[num_params]
  let minors = args[num_params + 1 : num_params + 1 + num_minors]
  // indices at args[num_params + 1 + num_minors : num_params + 1 + num_minors + num_indices]
  let major_idx = num_params + 1 + num_minors + num_indices
  let major = args[major_idx]
  let extra = args[major_idx + 1:]

  // WHNF the major premise to expose the constructor
  let major_whnf = self.whnf(major)
  let (ctor_head, ctor_args) = major_whnf.collect_app_args()
  let ctor_name = if ctor_head is Const(c) { c } else { return None }

  // Find which rule (constructor) this matches
  let rule_index = match rules.search_by(r => r.ctor == ctor_name) {
    Some(i) => i
    None => return None
  }

  let rule = rules[rule_index]

  // Extract constructor fields (skip params)
  let fields = ctor_args[num_params:]

  // Build the result: apply minor to fields and IHs
  let mut result = minors[rule_index]

  // To compute IH indices for recursive fields, we need to walk the constructor type
  // and instantiate params + prior fields to get each field's type
  let (_, ctor_ty) = ind.constructors[rule_index]

  // Instantiate params into constructor type
  let num_p = num_params
  let mut ctor_remaining = ctor_ty
  for i in 0..<num_p {
    ctor_remaining = instantiate(ctor_remaining, i.reinterpret_as_uint(), params[num_p - 1 - i])
  }

  // First pass: apply all fields to the minor, and collect IH terms for recursive fields
  let ih_terms: Array[Term] = []
  for k in 0..<rule.num_fields {
    result = App(result, fields[k])

    if rule.rec_fields.contains(k) {
      // Get the field's type from ctor_remaining to extract IH indices
      let field_ty = if ctor_remaining is Pi(_, a, _) { a } else { return None }
      let ih_indices = match extract_indices(field_ty, ind_name, num_params) {
        Some(idxs) => idxs
        None => return None
      }

      // Build IH: rec_name params... motive minors... ih_indices... field
      let mut ih = Const(rec_name)
      for p in params {
        ih = App(ih, p)
      }

      ih = App(ih, args[num_params]) // motive
      for m in minors {
        ih = App(ih, m)
      }

      for idx in ih_indices {
        ih = App(ih, idx)
      }

      ih = App(ih, fields[k])
      ih_terms.push(ih)
    }

    // Advance ctor_remaining by substituting this field into the Pi body
    if ctor_remaining is Pi(x, _, b) {
      ctor_remaining = if x is Some(_) {
        instantiate(b, 0, fields[k])
      } else {
        b
      }
    }
  }

  // Second pass: apply all IH terms
  for ih in ih_terms {
    result = App(result, ih)
  }

  // Re-apply excess args
  for a in extra {
    result = App(result, a)
  }

  Some(result)
}

// Weak Head Normal Form: only reduce the head of the term, and do not recurse under binders
pub fn Context::whnf(self: Context, term: Term) -> Term {
  match term {
    App(f, arg) => {
      // Only evaluate the function part to see if it's a Lam
      let f_whnf = self.whnf(f)
      match f_whnf {
        Lam(_, _, body) => self.whnf(instantiate(body, 0, arg))
        _ => {
          let result = Term::App(f_whnf, arg)
          let (head, args) = result.collect_app_args()
          match self.try_iota_reduce(head, args) {
            Some(reduced) => self.whnf(reduced)
            None => result
          }
        }
      }
    }
    Let(_, val, body) => {
      // zeta reduction
      self.whnf(instantiate(body, 0, val))
    }
    Const(name) => {
      if self.env.decls.get(name) is Some(decl) {
        match decl {
          // delta reduction
          Definition(_, body) => self.whnf(body)
          Axiom(_) | Inductive(_) | Constructor(_) | Recursor(_) => term
        }
      } else {
        Const(name)
      }
    }
    Ann(lhs, _) => self.whnf(lhs)
    Lam(_) | Pi(_) | Sort(_) | BoundVar(_) | FreeVar(_) => term
  }
}

fn instantiate(term: Term, idx: DeBruijnIndex, s: Term) -> Term {
  match term {
    BoundVar(i) if i == idx => s
    Lam(x, ty, body) => Lam(x, instantiate(ty, idx, s), instantiate(body, idx + 1, s))
    Pi(x, a, b) => Pi(x, instantiate(a, idx, s), instantiate(b, if x is Some(_) { idx + 1 } else { idx }, s))
    App(f, arg) => App(instantiate(f, idx, s), instantiate(arg, idx, s))
    Let(x, val, body) => Let(x, instantiate(val, idx, s), instantiate(body, idx + 1, s))
    Ann(lhs, rhs) => Ann(instantiate(lhs, idx, s), instantiate(rhs, idx, s))
    Sort(_) | Const(_) | BoundVar(_) | FreeVar(_) => term
  }
}

fn open(term: Term, idx: DeBruijnIndex, name: String, var_id: FreeVarId) -> Term {
  instantiate(term, idx, FreeVar(name, var_id))
}

fn close(term: Term, var_id: FreeVarId, idx: DeBruijnIndex) -> Term {
  match term {
    FreeVar(_, v_id) if v_id == var_id => BoundVar(idx)
    Lam(x, ty, body) => Lam(x, close(ty, var_id, idx), close(body, var_id, idx + 1))
    Pi(x, a, b) => Pi(x, close(a, var_id, idx), close(b, var_id, if x is Some(_) { idx + 1 } else { idx }))
    App(f, arg) => App(close(f, var_id, idx), close(arg, var_id, idx))
    Let(x, val, body) => Let(x, close(val, var_id, idx), close(body, var_id, idx + 1))
    Ann(lhs, rhs) => Ann(close(lhs, var_id, idx), close(rhs, var_id, idx))
    Sort(_) | Const(_) | BoundVar(_) | FreeVar(_) => term
  }
}

pub suberror TypeCheckError {
  TypeError(Term, String)
  DuplicateDeclaration(Name)
  FreeVarIdOverflow
}

pub impl Show for TypeCheckError with output(self: TypeCheckError, logger) -> Unit {
  match self {
    TypeError(term, message) => {
      logger.write_string("Type error when checking '\{term}': \{message}")
    }
    DuplicateDeclaration(name) => {
      logger.write_string("Duplicate declaration: '\{name}' is already declared")
    }
    FreeVarIdOverflow => {
      logger.write_string("Ran out of free variable IDs")
    }
  }
}

pub fn Context::infer(self: Context, term: Term) -> Term raise TypeCheckError {
  match term {
    Sort(u) => Sort(u + 1) // Prop : Type 0, Type u : Type (u + 1)
    Const(name) => {
      if self.env.decls.get(name) is Some(decl) {
        match decl {
          Axiom(ty) => ty
          // we already checked that the environment is well-formed
          Definition(ty, _) => ty
          Inductive({ ty, .. }) => ty
          Constructor(ty~, ..) => ty
          Recursor(ty~, ..) => ty
        }
      } else {
        raise TypeError(term, "Unbound reference '\{name}'")
      }
    }
    BoundVar(_) => raise TypeError(term, "BoundVar")
    FreeVar(_, var_id) => {
      if self.lookup_free_var(var_id) is Some(t) {
        t
      } else {
        raise TypeError(term, "Unbound variable '\{term}'")
      }
    }
    App(lhs, rhs) => {
      match self.whnf(self.infer(lhs)) {
        Pi(_, t0, t1) => {
          self.check(rhs, t0)
          instantiate(t1, 0, rhs)
        }
        lhs_ty => raise TypeError(term, "Expected LHS of application '\{term}' to be a Pi term, got '\{lhs_ty}'")
      }
    }
    Lam(x, arg_ty, body) => {
      let s1 = self.infer(arg_ty)
      if !(self.whnf(s1) is Sort(_)) {
        raise TypeError(term, "Invalid lambda argument type, got '\{s1}'")
      }

      let fresh_x = self.declare_fresh(arg_ty)
      defer self.free_vars.remove(fresh_x)
      let body_ty = self.infer(open(body, 0, x, fresh_x))
      let x = if body_ty.occurs_free(fresh_x) { Some(x) } else { None }

      Pi(x, arg_ty, close(body_ty, fresh_x, 0))
    }
    Pi(x, arg_ty, body_ty) => {
      let s1 = self.infer(arg_ty)
      let u1 = if self.whnf(s1) is Sort(u) {
        u
      } else {
        raise TypeError(term, "Invalid Pi argument type, got '\{s1}'")
      }

      let s2 = if x is Some(x) {
        let fresh_x = self.declare_fresh(arg_ty)
        defer self.free_vars.remove(fresh_x)
        close(self.infer(open(body_ty, 0, x, fresh_x)), fresh_x, 0)
      } else {
        self.infer(body_ty)
      }

      let u2 = if self.whnf(s2) is Sort(u) {
        u
      } else {
        raise TypeError(term, "Invalid Pi body type, got '\{s2}'")
      }

      Sort(if u2 == 0 {
        0 // Impredicativity: If the body is a Prop, the Pi is a Prop
      } else {
        u1.max(u2)
      })
    }
    Let(_, val, body) => {
      // check that val is well-typed
      let _ = self.infer(val)
      self.infer(instantiate(body, 0, val))
    }
    Ann(lhs, ty) => {
      let s = self.infer(ty)
      if !(self.whnf(s) is Sort(_)) {
        raise TypeError(term, "Invalid annotation type: \{ty}")
      }

      self.check(lhs, ty)
      ty
    }
  }
}

pub fn Context::check(self: Context, term: Term, ty: Term) -> Unit raise TypeCheckError {
  match term {
    _ => {
      let inferred_ty_norm = self.normalise(self.infer(term))
      let ty_norm = self.normalise(ty)
      if !self.is_def_eq(inferred_ty_norm, ty_norm) {
        raise TypeError(term, "Expected type '\{ty_norm}', got '\{inferred_ty_norm}'")
      }
    }
  }
}

// TODO: this is currently very naive and normalises both terms fully before comparing them, which is very inefficient.
// see https://rocq-prover.org/doc/V8.19.0/refman/language/core/conversion.html for how to do this more efficiently by interleaving reduction and comparison
// and only reducing as much as needed to determine definitional equality
pub fn Context::is_def_eq(self: Context, term: Term, expected: Term) -> Bool raise TypeCheckError {
  let t1_norm = self.normalise(term)
  let t2_norm = self.normalise(expected)

  if t1_norm.is_alpha_eq(t2_norm) {
    true
  } else {
    match (t1_norm, t2_norm) {
      // universes are cumulative: Type u <= Type v if u <= v
      (Sort(u1), Sort(u2)) => u1 <= u2
      (Pi(x1, a1, b1), Pi(x2, a2, b2)) => {
        if !self.is_def_eq(a1, a2) {
          return false
        }

        // Open both bodies with the same fresh FreeVar so they can be compared
        let fresh_x = self.declare_fresh(a1)
        defer self.free_vars.remove(fresh_x)

        let name1 = match x1 { Some(x) => x; None => "_" }
        let name2 = match x2 { Some(x) => x; None => "_" }
        let opened_b1 = open(b1, 0, name1, fresh_x)
        let opened_b2 = open(b2, 0, name2, fresh_x)

        self.is_def_eq(opened_b1, opened_b2)
      }
      _ => false
    }
  }
}

