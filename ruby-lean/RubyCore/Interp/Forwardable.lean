import RubyCore.Interp.Mutation

/-! Forwardable's source generator, for its simple accessor-expression fragment.
    The generated Proc contains a real `def` with `...` forwarding. It does not
    call define_method, capture accessor values, or bypass ordinary dispatch. -/
namespace RubyCore.Interp

def forwardableIdentifier (name : String) : Bool :=
  let chars := name.toList
  !chars.isEmpty && ((chars.headD '_').isAlpha || chars.headD '_' == '_') &&
    chars.all (fun c => c.isAlphanum || c == '_')

def forwardableMethodName (name : String) : Bool :=
  let base := if name.endsWith "?" || name.endsWith "!" || name.endsWith "=" then
    (name.dropEnd 1).toString else name
  forwardableIdentifier base ||
    ["[]", "[]=", "+", "-", "*", "/", "%", "**", "<<", ">>", "<=>", "<", ">", "<=", ">=",
     "==", "===", "!=", "!~", "=~", "!", "~", "-@", "+@", "&", "|", "^"].contains name

def forwardableAccessor (text : String) (isMethod : Bool) : Option Expr :=
  if isMethod then
    if forwardableMethodName text then some (.send none text [] none) else none
  else if text.startsWith "@" && !(text.startsWith "@@") then
    if forwardableIdentifier (text.drop 1).toString then some (.var .ivar text) else none
  else
    let absolute := text.startsWith "::"
    let parts := (if absolute then (text.drop 2).toString else text).splitOn "::"
    if parts.all (fun p => forwardableIdentifier p && (p.toList.headD '_').isUpper) then
      match parts with
      | [] => none
      | first :: rest =>
        some (rest.foldl (fun expr name => .cpath (some expr) name)
          (if absolute then .cpath none first else .const first))
    else if !absolute && forwardableIdentifier text then some (.vcall text)
    else none

/-- `_delegator_method` has already performed the public Ruby conversions and
    receiver-reflection calls before handing their results to this compiler. -/
def compileForwardable (m : Machine) (args : List Value) : StepResult :=
  if !m.currentFrame.libraryOrigin then .unsupported "internal Forwardable compiler" else
  if ["eval", "caller_locations"].any (fun name =>
      (lookup m.heap m.currentFrame.self name).any (fun (_, md) => md.builtin.isNone)) ||
      (lookup m.heap (.sym "") "to_s").any (fun (_, md) => md.builtin.isNone) then
    .unsupported "Forwardable source generation with user eval/location/Symbol conversion overrides" else
  match args with
  | [accessor, method, aliasName, isMethod, checked] =>
    if checked.truthy && m.stack.length <= 2 then
      .unsupported "Forwardable generator without a source caller location" else
    match symOrStr m accessor, symOrStr m method, symOrStr m aliasName with
    | some acc, some meth, some ali =>
      if !forwardableMethodName meth || !forwardableMethodName ali then
        .unsupported "Forwardable generated method syntax" else
      match forwardableAccessor acc isMethod.truthy with
      | none => .unsupported "Forwardable accessor expression needs general source compilation"
      | some access =>
        let target := Expr.var .lvar "_"
        let call := Expr.send (some target) meth [.fwd] none
        let body := if checked.truthy then
          Expr.seq [.vasgn .lvar "_" access,
            .if' (.defined (.send (some target) meth [] none)) call
              (some (.send none "__unsupported__" [.str "Forwardable warning path needs source locations and Kernel.warn"] none))]
          else Expr.send (some access) "__send__" [.sym meth, .fwd] none
        -- eval's default definee is its lexical class/module, not the owner
        -- of the singleton helper method. *_eval may rebind it when called.
        let original := m.currentFrame
        let capture := { original with defmod := original.cref.headD original.defmod }
        let captureId := m.frames.size
        let m := { m with frames := m.frames.push capture }
        let (value, m) := reifyBlock m [] [] (.def' ali [.fwd] body) false
        let m := match value with
          | .ref o => match (m.heap.get o).payload with
            | .proc cl => { m with heap := m.heap.set o { m.heap.get o with payload := .proc { cl with captured := some captureId } } }
            | _ => m
          | _ => m
        .next { m with ctl := .value value }
    | _, _, _ => .unsupported "Forwardable source compilation with non-name values"
  | _ => .unsupported "internal Forwardable compiler arity"

end RubyCore.Interp
