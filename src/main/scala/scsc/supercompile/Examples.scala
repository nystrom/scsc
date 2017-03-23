package scsc.supercompile

object Examples {
  // The main difference here is that the list is finite! Not sure it would terminate if not.
  // Cons 2 (Cons 2 (Cons 2 (Cons 2 (Cons 2 (Cons 2 Nil)))))
  val max1 = """
  let ones = Cons 1 (Cons 1 (Cons 1 (Cons 1 (Cons 1 (Cons 1 Nil))))) in letrec map = \f -> \xs -> case xs of Nil -> Nil | (Cons y ys) -> Cons (f y) (map f ys) in map (\x -> x+1) ones
  """

  // map inc xs --> specialize map on inc
  // currently just unrolls once
  // letrec map = \f -> \xs -> case xs of Nil -> Nil | Cons y ys -> Cons (f y) (map f ys)
  // in let xs = alist in
  //    case xs of Nil -> Nil
  //             | Cons y ys -> Cons (let x = y in x + 1)
  //                                 (let f = \x -> x + 1
  //                                  in let xs = ys
  //                                     in case xs of Nil -> Nil
  //                                                 | Cons y ys -> Cons (f y) (map f ys))
  //

  // Max's memoization: if state is a renaming of a previous state.
  // But here, we want to abstract away some of the continuation.
  // So, when arriving in a state, memoize the state with varying continuation
  // depths. If we get a match, we abstract that state into a function
  // and introduce a let.

  val max2 = """
  let inc = \x -> x + 1 in letrec map = \f -> \xs -> case xs of Nil -> Nil | (Cons y ys) -> Cons (f y) (map f ys) in map inc alist
  """

  // Just 3
  val max3 = """
  let x = True in let y = 1 + 2 in case x of True -> Just y | False -> Nothing
  """

  // 3
  val length1 = """
  letrec length = (\xs -> case xs of Nil -> 0 | (Cons x xs) -> 1 + (length xs)) in length (Cons 7 (Cons 8 (Cons 9 Nil)))
  """

  // 3
  val length1b = """
  letrec length = (\xs -> case xs of Nil -> 0 | (Cons x ys) -> 1 + (length ys)) in length (Cons 7 (Cons 8 (Cons 9 Nil)))
  """

  // 4
  val length1c = """
  letrec length = (\xs -> case xs of Nil -> 0 | (Cons x ys) -> 1 + (length ys)) in length (Cons a (Cons b (Cons c Nil)))
  """

  // 0
  val length2 = """
  letrec length = (\xs -> case xs of Nil -> 0 | (Cons x xs) -> 1 + (length xs)) in length Nil
  """

  // Nil
  val append1 = """
  letrec append = (\xs -> \ys -> case xs of Nil -> ys | (Cons x xs) -> (Cons x (append xs ys))) in (append Nil Nil)
  """

  // (Cons 1 (Cons 2 Nil))
  val append2 = """
  letrec append = (\xs -> \ys -> case xs of Nil -> ys | (Cons x xs) -> (Cons x (append xs ys))) in (append (Cons 1 Nil) (Cons 2 Nil))
  """

  // [[(let ys = (Cons x Nil) in (Cons 1 ys))]]
  val append3 = """
  letrec append = (\xs -> \ys -> case xs of Nil -> ys | (Cons x xs) -> (Cons x (append xs ys))) in (append (Cons 1 Nil) (Cons x Nil))
  """

  // [[(let ys = (Cons x Nil) in (Cons y ys))]]
  // Doesn't work!
  val append4 = """
  letrec append = (\xs -> \ys -> case xs of Nil -> ys | (Cons x xs) -> (Cons x (append xs ys))) in (append (Cons y Nil) (Cons x Nil))
  """

  // does not terminate
  val append5 = """
  letrec append = (\xs -> \ys -> case xs of Nil -> ys | (Cons z zs) -> (Cons z (append zs ys))) in (append as (append bs cs))
  """

  // does not terminate
  val append6 = """
  letrec append = (\xs -> \ys -> case xs of Nil -> ys | (Cons z zs) -> (Cons z (append zs ys))) in (append (append as bs) cs)
  """

  // [[(a * a * a)]]
  val pow1 = """
  letrec pow = (\x -> \n -> case n of 0 -> 1 | n -> (pow x (n-1)) * x) in (pow a 3)
  """

  // does not terminate
  val pow2 = """
  letrec pow = (\x -> \n -> case n of 0 -> 1 | n -> (pow x (n-1)) * x) in (pow 2 a)
  """

  // [[(let r = (a * (let r = (let r = a in (r * r)) in (r * r))) in (r * r))]]
  val logpow1 = """
  letrec pow = (\x -> (\n -> case n of 0 -> 1 | n -> case (n % 2) of 0 -> (let r = (pow x (n / 2)) in (r*r)) | 1 -> x * (pow x (n-1)))) in (pow a 10)
  """

  val logpow2 = """
  letrec pow = (\x -> (\n -> case n of 0 -> 1 | n -> case (n % 2) of 0 -> (let r = (pow x (n / 2)) in (r*r)) | 1 -> x * (pow x (n-1)))) in (pow a 3)
  """

  val fact10 = """
  letrec fact = \n -> case n of 0 -> 1 | m -> m * (fact (m-1)) in fact 10
  """

  val fib10 = """
  letrec fib = \n -> case n of 0 -> 1 | 1 -> 1 | m -> (fib (m-1)) + (fib (m-2)) in fib(10)
  """
}
