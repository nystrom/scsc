# From CESK to supercompilation and beyond

[This is a sketch of a submission to be made to POPL'18]

A CESK machine is an abstract machine consisting of four components: control, environment, state, and [k]ontinuation.
We describe a recipe for translating any CESK model into a supercompiler. We start with translating a CEK model, and extend to CESK. We then extend the supercompiler to support a further enhancement, distillation. We realize this theoretical model with an implementation of a supercompiler for JavaScript.

This paper also includes the first description of distillation using a non-process tree model.

## CEK and CESK machines

A CEK machine consists of three components: control, environment, and continuation. CEK machines can be used to model the dynamic semantics of functional and simple imperative programming languages. CESK extends CEK with a state component, allowing modelling of mutable state.

## Supercompilation 

Supercompilation is a partial evaluation technique that operates on process trees. At its simplest, supercompilation evaluates programs as much as possible at compile time. This is called _driving_ in the supercompilation literature. When evaluation cannot proceed from a given program state, the state is _split_ and evaluation is performed recursively. The supercompiler (conservatively) identifies states from which continued driving and splitting will not terminate and _generalizes_. This has the effect of making the process tree finite, allowing the algorithm to terminate. From the process tree, a program is extracted that implements the original program hopefully more efficiently.

Supercompilation has received a lot of attention in the functional programming literature because it subsumes common optimizations like deforestation. It is not yet in mainstream use in any functional language because of the following practical considerations: (1) supercompilation has a large compile time compared to traditional optimization, and (2) supercompilation can generate exponentially large code. Attempts to address these issues have been made in other work [taming-code-explosion], but not yet applied to a functional language such as Haskell.

## CEK machines

The state of the CEK machine:

    data Σ e ρ k = Σ e ρ k

Initial state:
    
    Σ e [] Done

`e` is the program we want to evaluate.
`[]` is the empty environment (keeping track of local variables).
`Done` is the empty continuation.

For the lambda calculus, we have `e` is just an expression. `k` is

    type Env = [(String, Value)]
    
    data Value = Closure Exp Env
    
    data Cont = Done
              | EvalArg Exp Env Cont
              | Call Exp Env Cont

Then the evaluation of the machine:

    step :: Σ Exp Env Cont -> Σ Exp Env Cont
    step (Σ (Var x) ρ k) =
        case lookup ρ x of
            Just (Closure e' ρ') -> Σ e' ρ' k
    step (Σ (App e1 e2) ρ k) =
        -- change the focus to the function e1
        -- when done, evaluate e2
        Σ e1 ρ (EvalArg e2 ρ k)
    step (Σ (Lam x e) ρ (EvalArg e' ρ' k) =
        -- done evaluating the function
        -- change the focus to the argument
        -- when done, call the function
        Σ e' ρ' (Call (Lam x e) e k)
    step (Σ (Lam x e) env (Call (Lam x' e') ρ' k) =
        -- done evaluating the argument (reduced to lambda)
        -- now call the function, passing in a closure for the argument
        Σ e' ρ'' k
          where ρ'' = (x', Closure (Lam x e) ρ):ρ'
    step state @ (Σ _ _ Done) = state
    step _ = error "no step defined"

To start:

    eval :: Exp -> State
    eval e = step (Σ e [] Done)
    
## From CEK to partial evaluation

Our starting point is an evaluator implemented using a CEK machine.

We extend the CEK machine to compute the residual directly.
Given expressions $e$, let the _residual_ $[\![e]\!]$ be a value.

We make the environment a partial environment, but then make it total again by returning the residual of a variable not in the environment. That is, if `x` is not in the environment, we return `[[x]]`.

    (x, ρ, k) --> (ρ(x), ρ, k)     if x in domρenv)
    (x, ρ, k) --> ([[x]], ρ, k)    otherwise

Once we have residual values, we have to work out how to compute with those value.
The simple implementation is to just compute the whole residual
from the continuation. We add rules for each continuation type to handle residual values, growing the residual whenever a "computation step" is performed.
> We say a step is a "computation step" if it performs an operation and pops the continuation. A "congruence step" pushes a new continuation and changes the focus.

    -- computation steps added to grow the residual
    ([[e]], ρ, v+[] then k) --> ([[v+e]], ρ, k)
    ([[e]], ρ, v [] then k) --> ([[v e]], ρ, k)
    
    -- congurence steps are unchanged
    (v, ρ, []+e' then k) --> (e', ρ, v+[] then k)
    (v, ρ, [] e' then k) --> (e', ρ, v [] then k)
    
But, we can do better. For instance, rather than just residualizing the call, we can inline functions by adding the residual value to the environment and evaluating the function body.

    ([[e]], ρ, (\x.e') [] then k) --> (e', ρ + (x -> [[e]]), k)

This works for call-by-name semantics: It substitutes the argument into the body of the function. But, for call-by-value or call-by-need semantics, we need a linearity check. If we pass a residual to a function, that
function might use its parameter multiple times, duplicating the residual in the output expression.
So, we can introduce a `let` when we apply a function with a residual argument.

    ([[e]], ρ (\x.e') [] then k) --> (e', ρ + (x -> [[x]]), make-let x e then k)
    (v, ρ, make-let x e then k) --> ([[let x = e in v]], ρ, k)
    
Then we need to support `make-let` continuations for lets with residual values.
Here are the usual rules for `let`:

    (let x = e1 in e2, ρ, k) --> (e1, ρ, let-cont x e2 then k)
    (v, ρ, let-cont x e2 then k) --> (e2, ρ + (x -> v), k)
    
To avoid sharing, we add the following rule that fires for residual values.
We can special case this to inline (as above) when safe. The residual has to be _pure_, _total_, and preferably _cheap_.

    ([[e]], ρ, let-cont x e2 then k) --> (e2, ρ + (x -> [[x]]), make-let x e then k)
  
> Can we use a "store" trick (like the continuation pointers of CESK*) to fix the sharing problem? We make a "store" containing residual expressions.

## Splitting and let floating

As an optimization we can float `let`s in the residual outward.
We do this simply by pushing `make-let` continuations down into the continuation when variable capture cannot occur. For instance:

    (v, ρ, make-let x e then []+e' then k) --> (e', ρ, v+[] then make-let x e then k)
    (v, ρ, make-let x e then [] e' then k) --> (e', ρ, v [] then make-let x e then k)

> Not sure about this now!
A benefit of let floating is that we can compute under the `let`.
Consider:

    (f, ρ[f = \x -> x], make-let f (\x -> x) then [] 1)
    ->
    (\x -> x, ρ[f = \x -> x], make-let f (\x -> x) then [] 1)
    ->
    (\x -> x, ρ, [] 1)
    ->
    (1, ρ, Done)

Consider:

    (let f = \x -> x in f) 1

If we float the let, we get:

    let f = \x -> x in (f 1)

which evaluates to 1.


Note, we don't actually need the environment anymore. We can just lookup variables in the continuation! `make-let` can be simplified to `make-frame` perhaps without recording the value because we can lookup in the environment. Or vice versa.

But, we need the environment to distinguish `x -> v` vs `x -> [[x]]`. The latter is needed for supporting non-linear expressions in CBV or CBNeed.


## Partial evaluation with termination

The partial evaluation scheme described above may not terminate. If we partially evaluate an expression 

To ensure termination, need to detect when repeating ourselves.
If `e` is a repeat, we step to `[[e]]`, which (as a value) will avoid recomputing `e` and we eventually terminate the machine outputting a residual expression.

Naive solution: We can ensure termination of the machine by maintaining a counter in the state. We add a tick to the state and initialize to some threshold.

    c e k t
    
Each step, we decrement the tick. Then when the machine times out, we perform the following transition for `e` not a value.
    
    (e, ρ, k, 0) --> ([[e]], ρ, k, 0)

To ensure the residual is computed correctly we **must** add a `make-let` continuation every time the environment is extended. However, `make-let` does not need to actually reify the `let` if the variable is not free in the focus. We modify the rule as follows

    (v, ρ, make-let x e then k) --> ([[let x = e in v]], ρ, k)
        if x in fv(v)
    (v, ρ, make-let x e then k) --> (v, ρ, k)
        if x not in fv(v)

### The whistle

In each state, we residualize the state to a term and compare against previous terms.
If there is a homeomorphic embedding of a previous term in the current term, we blow the whistle.

To residualize a state to a term, we simply evaluate the term on the CEK machine, but after each step, we residualize the focus term. This includes residualizing lambdas (otherwise we might not terminate). 

Need to prove a theorem that replacing an expression by its residualization
at each step will terminate in a finite number of steps. This gives us an algorithm for computing an expression from a state.

## Partial evaluation with termination to supercompilation

Different termination whistle (less ad hoc). Then introduce generalization.

## From supercompilation to distillation

Different generalization.

## OLD OLD OLD

We need a way to reconstruct the term from the state, regardless of the state.

We need to be able to construct a state from a term and reconstruct a term from a state.

    inject :: t -> Σ c e k
    eject :: Σ c e k -> t
    
Typically the control component is just a term, so:

    inject c = Σ c [] Done
    eject (Σ c e k) = let e in k[c]

`eject` assumes the term language supports `let`. We can 
also implement this using top-level definitions, but maybe
we'll need to do closure conversion to make that work?

Reconstruction in the distillation paper is straightforward
(as above), except for function call (in context) and repeat edges.

For a function call (the body of the function `f` is `t`).

    C [[ a = con<f> ---> t ]]
        | there is a b s.t. t.b --> a =
          letrec f' = \v1..vn -> C [[ t ]]
          in f' v1 ... vn
          
          where b = a{v1=e1 ... vn=en}
        | otherwise = C [[ t ]]

For repeat edges:

    C [[ b = con<f> -:-> a ]]
        = f' e1 ... en
            
          where b = a{v1=e1 ... vn=en}

Repeat edges are added when we see an alpha-renamed state in the history. This is memoization in Max's version (when we see an alpha-renamed state, we just return the memoized state renamed).

Also (performs beta reduction):

    C [[ con< (\x -> e0) e1 > --> t ]] = C [[ t ]]

So, we run the steps until we reach a particular state
and then reconstruct the state into a term.

Now, let's look at an alternative formulation based on process trees.

We start with the CEK machine definition.
We want to build a process tree from the definition.

A process tree is a DAG where each node is labeled with an expression and edges leaving a node are ordered. For tree t and node a, t(a) is the label of a (i.e., an expression), anc(t,a) denotes the set of ancestors of a in t, t{a := t'} is the tree obtained by replacing root a in t with t'. Finally e -> t1..tn is the tree labeled e with n children, the subtrees t1..tn.

A partial process tree may have repeat nodes with back edges.

e' <= e if e' can be alpha-renamed to e

Repeat nodes correspond to a fold step... when a term is encountered that is an alpha rename of an ancestor, we create a repeat node. The ancestor is called a function node.

The distillation paper describes supercompilation as building the process tree. 

we evaluate each expression to a list of redexes in the expression. these are the children in the process tree
in the case of function references, the child is the body of the function

to support generalization we introduce let expressions.


Plus the taming code explosion issue too!



precondition:

- present a supercompiler in a way that a master student (or Matthias) can implement it

- framework that maps the process tree model to the evaluation model and back
- show they're equivalent

-----

### From evaluation to partial evaluation to supercompilation

Can we separate out the termination and memoization and generalization and (linearity) issues?

Splitting. Splitting we do for configurations where we can't make progress. `if` where the condition is not known, etc.

For Luis: write a CESK-style evaluator for JS.
Extend to be a partial evaluator.
Extend the PE to handle termination and generalization in a nice way. The distillation.
Extend the PE with splitting. Supercompilation!
Extend the PE with generalization.

Need proofs of correctness :-(


First let's derive a PE from a CESK machine.


Distillation using LTS.
Put labels on the reduction relation.
    
    f -->[f] e
    (\x.e0) e1 -->[\downarrow e1] e0[x:=e1]
    
    e -->[t] e'
    ------------------
    E[e] -->[t] E[e']
    
    p = c ..xi..
    ------------------
    case (c ..ei..) of ..pi -> ei'
        -->[c] ei'[..xi.. := ..ei..]
        
This is just the usual reduction rules labeled with f if a function
is applied and c if a pattern with constructor c is matched and \downarrow e1 if we pass e1 as an argument to a lambda


Apply the driving rules D to e to get an LTS.
Apply transformation rules T to the LTS.
These work lazily from the root. If non-termination of the transformation
is detected, generalization is performed.
Effect of generalization is that a renaming of a previously encountered LTS will be encountered. There we do "folding" to convert the current LTS into a finite LTS.
Then R residualizes the finite folded LTS.

Paper says: Main difference between distillation and positive supercompilation is that generalization and folding are performed WRT LTSs in distillation and WRT to expressions in positive supercompilation.


Generalization.
LTS t1 is embedded within t2 by diving and coupling. This is just HE applied to LTS.

Is the CESK machine just a summarization of an LTS? Hmm.


 


## From CESK to supercompilation

CESK adds a store to CEK.
But also removes the recursive structure of the environment.
Because now the environment maps variables to addresses, not closures. Closures live in the store.

## From CESK to distillation

## Distilling JavaScript

We apply our technique to a CESK model of JavaScript, deriving a distillation algorithm. We have implemented this algorithm in a caching proxy server. Experiments below.

## Future work

Extending with constraints.

## Citations


Abstracting abstract machines. David Van Horn, Matthew Might.
