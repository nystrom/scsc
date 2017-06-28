# From abstract machines to supercompilation and beyond

Supercompilation is a partial evaluation technique
primarily used today for program optimization in functional languages. Supercompilation extends traditional partial evaluation by recognizing repeated computations and generalizing to ensure the partial evaluator terminates. We describe a recipe for translating an abstract machine model into a supercompiler. We start with Felleisen's CEK model, extending the model with _residual values_. We then describe extending the recipe to handle mutable state. We demonstrate the approach by implementing a supercompiler for JavaScript and show its optimization potential on the JSBench suite.


The JavaScript partial evaluator first desugars into LambdaS5, which is considerably simpler. We then implement a PE for LambdaS5.

## CEK and CESK machines

A CEK machine consists of three components: control, environment, and continuation. CEK machines can be used to model the dynamic semantics of functional and simple imperative programming languages. CESK extends CEK with a state component, allowing modelling of mutable state.

## Supercompilation 

Supercompilation is a partial evaluation technique that operates on process trees. At its simplest, supercompilation evaluates programs as much as possible at compile time. This is called _driving_ in the supercompilation literature. When evaluation cannot proceed from a given program state, the state is _split_ and evaluation is performed recursively. The supercompiler (conservatively) identifies states from which continued driving and splitting will not terminate and _generalizes_. This has the effect of making the process tree finite, allowing the algorithm to terminate. From the process tree, a program is extracted that implements the original program hopefully more efficiently.

Supercompilation has received a lot of attention in the functional programming literature because it subsumes common optimizations like deforestation. It is not yet in mainstream use in any functional language because of the following practical considerations: (1) supercompilation has a large compile time compared to traditional optimization, and (2) supercompilation can generate exponentially large code. Attempts to address these issues have been made in other work [taming-code-explosion], but not yet applied to a functional language such as Haskell.

Our aim in the paper is to try to present a form of supercompilation using a simpler (at least for us) abstraction than process trees, namely abstract machines. Using a simpler model, we believe supercompilation can be more easily explained and more easily adapted to other programming languages for which such a model exists. 

This work follows in the spirit of [abstracting-abstract-machines].

We first describe how an abstract machine, namely a CEK machine, can be transformed into a simple partial evaluator by introducing _residual values_.
Performing a computation step on a residual value results in another residual value. We then describe how we can implement generalization on top of the CEK machine, yielding a supercompiler.

Adding state to a CEK machine yields a CESK machine. We show our approach can be extended to a CESK machine, describing supercompilation for a simple imperative language.

Finally, we extend a JavaScript interpreter, implemented in a CESK style to support supercompilation for JavaScript programs.

JavaScript is a notoriously difficult language to implement, with a complex semantics for even the simplest operations. However, one advantage of implementing a partial evaluator versus a interpreter is that the difficult cases can be residualized: that is, rather than implement the precise semantics for some language features, they can be ignored and left in the residual program.

Our JS implementation uses some of the desugarings from Lambda JS [lambda-js].


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

Proof. In a finite number of steps, the continuation shrinks.
If the focus is a residual. Either the continuation stays the same
size and the focus changes to another residual.
Or the continuation shrinks.
The focus never changes back the same residual.
Heap lookups are never performed since variables are initialized immediately.

## Partial evaluation with termination 

Different termination whistle (less ad hoc). Then introduce generalization.

## Adding generalization

Residualize the state.
Perform HE on the terms.

## Adding state

CESK machine for IMP
    
    e ::= v | x | e op e
        | while (e) e | if (e) then e else e
        | var x = e; e | x = e | e; e
        | v
    v ::= n | true | false | loc

The main point to notice is that var allocates a location and adds x to the scope.

Technically for this language we don't need locations, we can just use names, but modelling locations explicitly makes it easier to extend with heap data structures.
 

    (e1; e2, rho, sigma, k)
    -->
    (e1, rho, sigma, (then e2 rho)::k)
    
    (v, rho, sigma, (then e2 rho')::k)
    -->
    (e2, rho', sigma, k)
    
    (while (e1) e2, rho, sigma, k)
    -->
    (if (e1) (e2; while (e1) e2), rho, sigma, k)

    (if (e0) then e1 else e2, rho, sigma, k)
    -->
    (e0, rho, sigma, (branch e1 e2 rho)::k)
    
    (true/false, rho, sigma, (branch e1 e2 rho')::k)
    -->
    (e1/e2, rho', sigma, k)
        
    (var x = e1; e2, rho, sigma, k)
    -->
    (x = e1, rho', sigma', (then e2 rho')::k) 
        rho' = rho[x := loc], loc fresh
        sigma' = sigma[loc := false]

    (x = e, rho, sigma, k)
    -->
    (rho(x), rho, sigma, (eval-rhs e rho)::k)

    (v, rho, sigma, (eval-rhs e rho')::k)
    -->
    (e, rho', sigma, (assign v rho)::k)

    (v, rho, sigma, (assign loc rho')::k)
    -->
    (v, rho', sigma[loc := v], k)

    (x, rho, sigma, k)
    -->
    (sigma(rho(x)), rho, sigma, k)

    (e1 op e2, rho, sigma, k)
    -->
    (e1, rho, sigma, (eval-right op e2 rho)::k)
    
    (v1, rho, sigma, (eval-right op e2 rho')::k)
    -->
    (e2, rho', sigma, (eval-op op v1 rho')::k)
    
    (v2, rho, sigma, (eval-op op v1 rho')::k)
    -->
    (v1 `op` v2, rho', sigma, k)
    
`op` is defined to do the arithmetic operation as usual.

Extending with residual values:

    v ::= ... | [[e]]
    
We add the following rules:

    ([[e1]], rho, sigma, (then e2 rho')::k)
    -->
    (e2, rho', sigma, (make-; e1 rho')::k)
    
    (v2, rho, sigma, (make-; e1 rho')::k)
    -->
    ([[e1; v2]], rho', sigma, k)

Handling if is more complicated. If the condition is a residual,
we evaluate the true branch but with a continuation that evaluates the false branch then rebuilds the if.
We save the store sigma in the continuation so we can evaluate both branches
in the same store.

    ([[e]], rho, sigma, (branch e1 e2 rho')::k)
    -->
    (e1, rho', sigma, (eval-false-then-make-if e e2 sigma rho')::k)

After the true branch is evaluated, we evaluate the false branch,
with a continuation that rebuilds the if.
We save the store again, this time for the state after the true branch.

    (v1, rho, sigma, (eval-false-then-make-if e0 e2 sigma' rho')::k)
    -->
    (e2, rho', sigma', (make-if e0 v1 sigma rho')::k)

Now we've evaluated both the true and false branches.
We recreate the if.

    (v2, rho, sigma, (make-if e0 e1 sigma' rho')::k)
    -->
    ([[if e0 then e1 else v2]], rho', sigma'', k)
        where sigma'' = merge(sigma, sigma')
    
We merge the stores that result after the two branches.
We describe store merging later.

Assignment is extended to handle residual values:

    (v, rho, sigma, (assign [[e]] rho')::k)
    -->
    ([[e = v]], rho', sigma', k)
        where sigma' = sanitize(rho', sigma')  # remove anything accessible from rho', which was the environment of e

If a variable x is not in rho, or its location is not in sigma,
we residualize the variable.

    (x, rho, sigma, k)
    -->
    ([[x]], rho, sigma, k)

This rule allows computation on open expressions.
If a variable is not found in the environment or in the store, we just residualize it.

Then for binary expressions:

    (v2, rho, sigma, (eval-op op v1 rho')::k)
    -->
    ([[v1 op v2]], rho', sigma, k)
        where v1 or v2 is a residual
        
        
One catch is that after residualizing a variable `x`, we must ensure
its declaration is in the residual.
To ensure that, we add the following rule:

    ()

## Proof of correctness

Can do this proof for CEK. For CESK too, if we can state the theorem correctly.

    if s1 -->* s2 in the original machine
    and s1 -->* s2' in the new machine
        where we arbitrarily add an x --> [[x]] transition
    then
    s2' -->* s2 in the original machine
    
Proof by bisimulation.???

## Extending IMP with arrays

## Generalizing with state


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
Extend the PE to handle termination and generalization in a nice way. Then distillation.
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
