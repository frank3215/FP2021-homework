
Agda is a dependently typed language based on intuitionistic type theory
developed at Chalmers University in Gothenburg. This section introduces the
basic features of Agda and how they can be employed in the construction of
dependently typed programs. Information on how to obtain the Agda system
and further details on the topics discussed here can be found on the Agda
wiki~\cite{agda:wiki}.

This section is a literate Agda file which can be compiled by the Agda
system. Hence, we need to start at the beginning: Every Agda file contains
a single top-level module whose name corresponds to the name of the file.
In this case the file is called {\tt AgdaBasics.lagda}\footnote{Literate
Agda files have the extension {\tt lagda} and ordinary Agda files have the
extension {\tt agda}.}.

\begin{code}
module AgdaBasics where
\end{code}

The rest of your program goes inside the top-level module. Let us start by
defining some simple datatypes and functions.

\subsection{Datatypes and pattern matching} \label{Datatypes}

Similar to languages like Haskell and ML, a key concept in Agda is pattern matching
over algebraic datatypes. With the introduction of dependent types pattern matching
becomes even more powerful as we shall see in Section~\ref{Families} and
Section~\ref{ProgrammingTechniques}. But for now, let us start with simply typed 
functions and datatypes.

Datatypes are introduced by a \verb!data! declaration, giving the name and type of
the datatype as well as the constructors and their types. For instance, here is the
type of booleans

\begin{code}
data Bool : Set where
  true  : Bool
  false : Bool
\end{code}

The type of \verb!Bool! is \verb!Set!, the type of small\footnote{There is hierarchy
of increasingly large types. The type of {\tt Set} is {\tt Set1}, whose type is
{\tt Set2}, and so on.} types. Functions over \verb!Bool! can be defined by pattern
matching in a for Haskell programmers familiar way:

\begin{code}
not : Bool -> Bool
not true  = false
not false = true
\end{code}

Agda functions are not allowed to crash, so a function definition must
cover all possible cases. This will be checked by the type checker and an
error is raised if there are missing cases.

In Haskell and ML the type of \verb!not! can be inferred from the defining
clauses and so in these languages the type signature is not required.
However, in the presence of dependent types this is no longer the case and
we are forced to write down the type signature of \verb!not!. This is not a
bad thing, since by writing down the type signature we allow the type checker,
not only to tell us when we make mistakes, but also to guide us in the
construction of the program. When types grow more and more precise the dialog
between the programmer and the type checker gets more and more interesting.

Another useful datatype is the type of (unary) natural numbers.

\begin{code}
data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
\end{code}

Addition on natural numbers can be defined as a recursive function.

\begin{code}
_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)
\end{code}

In the same way as functions are not allowed to crash, they must also be
terminating. To guarantee termination recursive calls have to be made on
structurally smaller arguments. In this case \verb!_+_! passes the
termination checker since the first argument is getting smaller in the
recursive call ($\verb!n! < \verb!suc n!$). Let us define multiplication
while we are at it

\begin{code}
_*_ : Nat -> Nat -> Nat
zero  * m = zero
suc n * m = m + n * m
\end{code}

Agda supports a flexible mechanism for mixfix operators. If a name of a
function contains underscores (\verb!_!) it can be used as an operator with
the arguments going where the underscores are. Consequently, the function
\verb!_+_! can be used as an infix operator writing \verb!n + m! for
\verb!_+_ n m!. There are (almost) no restrictions on what symbols are
allowed as operator names, for instance we can define

\begin{code}
_or_ : Bool -> Bool -> Bool
true  or x = x
false or _ = false

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y
\end{code}

In the second clause of the \verb!_or_! function the underscore is a
wildcard pattern, indicating that we don't care what the second argument is
and we can't be bothered giving it a name. This, of course, means that we
cannot refer to it on the right hand side. The precedence and fixity of an
operator can be declared with an \verb!infix! declaration:

\begin{code}
infixl 60 _*_
infixl 40 _+_
infixr 20 _or_
infix  5 if_then_else_
\end{code}

There are some new and interesting bits in the type of
\verb!if_then_else_!. For now, it is sufficient to think about
\verb!{A : Set} ->! as declaring a polymorphic function over a type
\verb!A!. More on this in Sections \ref{DependentTypes} and
\ref{Implicit}.

Just as in Haskell and ML datatypes can be parameterised by other
types. The type of lists of elements of an arbitrary type is defined by

\begin{code}
infixr 40 _::_
data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A
\end{code}

Again, note that Agda is quite liberal about what is a valid name. Both
\verb![]! and \verb!_::_! are accepted as sensible names. In fact, Agda
names can contain arbitrary non-whitespace unicode characters, with a few
exceptions, such as parenthesis and curly braces. So, if we
really wanted (which we don't) we could define the list type as

\begin{code}
data _⋆ (α : Set) : Set where
  ε : α ⋆
  _◁_ : α -> α ⋆ -> α ⋆
\end{code}

This liberal policy of names means that being generous with whitespace
becomes important. For instance, \verb!not:Bool->Bool! would not be a valid
type signature for the \verb!not! function, since it is in fact a valid name.

\subsection{Dependent functions} \label{DependentTypes}

Let us now turn our attention to dependent types. The most basic dependent
type is the dependent function type, where the result type depends on the
value of the argument. In Agda we write \verb!(x : A) -> B! for the type of
functions taking an argument \verb!x! of type \verb!A! and returning a
result of type \verb!B!, where \verb!x! may appear in \verb!B!. A special
case is when \verb!x! itself is a type. For instance, we can define

\begin{code}
identity : (A : Set) -> A -> A
identity A x = x

zero' : Nat
zero' = identity Nat zero
\end{code}

This is a dependent function taking a type argument \verb!A! and an element
of \verb!A! and returns the element. This is how polymorphic functions are
encoded in Agda. Here is an example of a more intricate dependent function;
the function which takes a dependent function and applies it to an
argument:

\begin{code}
apply : (A : Set)(B : A -> Set) ->
        ((x : A) -> B x) -> (a : A) -> B a
apply A B f a = f a
\end{code}

Agda accepts some short hands for dependent function types:

\begin{itemize}
  \item {\small \verb!(x : A)(y : B) -> C! } for
        {\small \verb!(x : A) -> (y : B) -> C! }, and
  \item {\small \verb!(x y : A) -> B! } for
        {\small \verb!(x : A)(y : A) -> B! }.
\end{itemize}

The elements of dependent function types are lambda terms which may carry
explicit type information. Some alternative ways to define the identity
function above are:

\begin{code}
identity₂ : (A : Set) -> A -> A
identity₂ = \A x -> x

identity₃ : (A : Set) -> A -> A
identity₃ = \(A : Set)(x : A) -> x

identity₄ : (A : Set) -> A -> A
identity₄ = \(A : Set) x -> x
\end{code}

\subsection{Implicit arguments} \label{Implicit}

We saw in the previous section how dependent functions taking types as
arguments could be used to model polymorphic types. The thing with
polymorphic functions, however, is that you don't have to say at which type
you want to apply it -- that is inferred by the type checker. However, in
the example of the identity function we had to explicitly provide the type
argument when applying the function. In Agda this problem is solved by a
general mechanism for {\em implicit arguments}. To declare a function
argument implicit we use curly braces instead of parenthesis in the type:
\verb!{x : A} -> B! means the same thing as \verb!(x : A) -> B! except
that when you use a function of this type the type checker will try to
figure out the argument for you.

Using this syntax we can define a new version of the identity function,
where you don't have to supply the type argument.

\begin{code}
id : {A : Set} -> A -> A
id x = x

true' : Bool
true' = id true
\end{code}

Note that the type argument is implicit both when the function is applied
and when it is defined.

There are no restrictions on what arguments can be made implicit, nor are
there any guarantees that an implicit argument can be inferred by the type
checker. For instance, we could be silly and make the second argument of
the identity function implicit as well:

\begin{code}
silly : {A : Set}{x : A} -> A
silly {_}{x} = x

false' : Bool
false' = silly {x = false}
\end{code}

Clearly, there is no way the type checker could figure out what the second
argument to \verb!silly! should be. To provide an implicit argument
explicitly you use the implicit application syntax \verb!f {v}!, which
gives \verb!v! as the left-most implicit argument to \verb!f!, or as shown
in the example above, \verb!f {x = v}!, which gives \verb!v! as the
implicit argument called \verb!x!. The name of an implicit argument
is obtained from the type declaration.

Conversely, if you want the type checker to fill in a term which needs to
be given explicitly you can replace it by an underscore. For instance,

\begin{code}
one : Nat
one = identity _ (suc zero)
\end{code}

It is important to note that the type checker will not do any kind of
search in order to fill in implicit arguments. It will only look at the
typing constraints and perform unification\footnote{Miller pattern
unification to be precise.}.

Even so, a lot can be inferred automatically. For instance, we can define
the fully dependent function composition. (Warning: the following type is
not for the faint of heart!)
 
\begin{code}
_∘_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set}
      (f : {x : A}(y : B x) -> C x y)(g : (x : A) -> B x)
      (x : A) -> C x (g x)
(f ∘ g) x = f (g x)

plus-two = suc ∘ suc
\end{code}

The type checker can figure out the type arguments \verb!A!, \verb!B!, and
\verb!C!, when we use \verb!_∘_!.

We have seen how to define simply typed datatypes and functions, and how to
use dependent types and implicit arguments to represent polymorphic
functions. Let us conclude this part by defining some familiar functions.

\begin{code}
map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)
\end{code}

\subsection{Datatype families} \label{Families}

So far, the only use we have seen of dependent types is to represent
polymorphism, so let us look at some more interesting examples. The type of
lists of a certain length, mentioned in the introduction, can be defined as
follows:

\begin{code}
data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)
\end{code}

This declaration introduces a number of interesting things. First, note
that the type of \verb!Vec A! is \verb!Nat -> Set!. This means that
\verb!Vec A! is a family of types indexed by natural numbers. So, for each
natural number \verb!n!, \verb!Vec A n! is a type. The constructors are
free to construct elements in an arbitrary type of the family. In
particular, \verb![]! constructs an element in \verb!Vec A zero! and
\verb!_::_! an element in \verb!Vec A (suc n)! for some \verb!n!.

There is a distinction between {\em parameters} and {\em indices} of a
datatype. We say that \verb!Vec! is parameterised by a type \verb!A! and
indexed over natural numbers.

In the type of \verb!_::_! we see an example of a dependent function
type. The first argument to \verb!_::_! is an implicit natural number
\verb!n! which is the length of the tail. We can safely make \verb!n!
implicit since the type checker can infer it from the type of the third
argument.

Finally, note that we chose the same constructor names for \verb!Vec! as
for \verb!List!. Constructor names are not required to be distinct between
different datatypes.

Now, the interesting part comes when we start pattern matching on elements
of datatype families. Suppose, for instance, that we want to take the head
of a non-empty list. With the \verb!Vec! type we can actually express the
type of non-empty lists, so we define \verb!head! as follows:
%
\begin{code}
head : {A : Set}{n : Nat} -> Vec A (suc n) -> A
head (x :: xs) = x
\end{code}
%
This definition is accepted by the type checker as being exhaustive,
despite the fact that we didn't give a case for \verb![]!. This is
fortunate, since the \verb![]! case would not even be type correct -- the
only possible way to build an element of \verb!Vec A (suc n)! is using the
\verb!_::_! constructor.

The rule for when you have to include a particular case is very simple:
{\em if it is type correct you have to include it}.

\subsubsection{Dot patterns}

Here is another function on \verb!Vec!:

\begin{code}
vmap : {A B : Set}{n : Nat} -> (A -> B) -> Vec A n -> Vec B n
vmap f []        = []
vmap f (x :: xs) = f x :: vmap f xs
\end{code}

Perhaps surprisingly, the definition map on \verb!Vec! is exactly the same
as on \verb!List!, the only thing that changed is the type. However,
something interesting is going on behind the scenes. For instance, what
happens with the length argument when we pattern match on the list? To see
this, let us define new versions of \verb!Vec! and \verb!vmap! with fewer
implicit arguments:

\begin{code}
data Vec₂ (A : Set) : Nat -> Set where
  nil  : Vec₂ A zero
  cons : (n : Nat) -> A -> Vec₂ A n -> Vec₂ A (suc n)

vmap₂ : {A B : Set}(n : Nat) -> (A -> B) -> Vec₂ A n -> Vec₂ B n
vmap₂ .zero    f nil           = nil
vmap₂ .(suc n) f (cons n x xs) = cons n (f x) (vmap₂ n f xs)
\end{code}

What happens when we pattern match on the list argument is that we learn
things about its length: if the list turns out to be \verb!nil! then the
length argument must be \verb!zero!, and if the list is \verb!cons n x xs!
then the only type correct value for the length argument is \verb!suc n!.
To indicate that the value of an argument has been deduced by type
checking, rather than observed by pattern matching it is prefixed by a dot
(\verb!.!).

In this example we could choose to define \verb!vmap! by first pattern
matching on the length rather than on the list. In that case we would put
the dot on the length argument of \verb!cons!\footnote{In fact the dot can
be placed on any of the {\tt n}s. What is important is that there is a
unique binding site for each variable in the pattern.}:

\begin{code}
vmap₃ : {A B : Set}(n : Nat) -> (A -> B) -> Vec₂ A n -> Vec₂ B n
vmap₃ zero    f nil            = nil
vmap₃ (suc n) f (cons .n x xs) = cons n (f x) (vmap₃ n f xs)
\end{code}

The rule for when an argument should be dotted is: {\em if there is a
unique type correct value for the argument it should be dotted}.

In the example above, the terms under the dots were valid patterns, but in
general they can be arbitrary terms. For instance, we can define the image
of a function as follows:

\begin{code}
data Image_∋_ {A B : Set}(f : A -> B) : B -> Set where
  im : (x : A) -> Image f ∋ f x
\end{code}

Here we state that the only way to construct an element in the image of
\verb!f! is to pick an argument \verb!x! and apply \verb!f! to
\verb!x!. Now if we know that a particular \verb!y! is in the image of
\verb!f! we can compute the inverse of \verb!f! on \verb!y!:

\begin{code}
inv : {A B : Set}(f : A -> B)(y : B) -> Image f ∋ y -> A
inv f .(f x) (im x) = x
\end{code}

\subsubsection{Absurd patterns}

Let us define another datatype family, name the family of numbers smaller
than a given natural number.

\begin{code}
data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)
\end{code}

Here \verb!fzero! is smaller than \verb!suc n! for any \verb!n! and if
\verb!i! is smaller than \verb!n! then \verb!fsuc i! is smaller than
\verb!suc n!. Note that there is no way of constructing a number smaller
than zero. When there are no possible constructor patterns for a given argument
you can pattern match on it with the absurd pattern \verb!()!:

\begin{code}
magic : {A : Set} -> Fin zero -> A
magic ()
\end{code}

Using an absurd pattern means that you do not have to give a right hand
side, since there is no way anyone could provide an argument to your
function. One might think that the clause would not have to be given at
all, that the type checker would see that the matching is exhaustive
without any clauses, but remember that a case can only be omitted if there
is no type correct way of writing it. In the case of \verb!magic! a
perfectly type correct left hand side is \verb!magic x!.

It is important to note that an absurd pattern can only be used
if there are no valid constructor patterns for the argument, it is not
enough that there are no closed inhabitants of the type\footnote{Since
checking type inhabitation is undecidable.}. For instance, if we define

\begin{code}
data Empty : Set where
  empty : Fin zero -> Empty
\end{code}

Arguments of type \verb!Empty! can not be matched with an absurd pattern,
since there is a perfectly valid constructor pattern that would do:
\verb!empty x!. Hence, to define the \verb!magic! function for \verb!Empty!
we have to write

\begin{code}
magic' : {A : Set} -> Empty -> A
magic' (empty ())
-- magic' ()  -- not accepted
\end{code}

Now, let us define some more interesting functions. Given a list of length
\verb!n! and a number \verb!i! smaller than \verb!n! we can compute the
\verb!i!th element of the list (starting from 0):

\begin{code}
_!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
[]        ! ()
(x :: xs) ! fzero    = x
(x :: xs) ! (fsuc i) = xs ! i
\end{code}

The types ensure that there is no danger of indexing outside the list. This
is reflected in the case of the empty list where there are no possible
values for the index.

The \verb+_!_+ function turns a list into a function from indices to
elements. We can also go the other way, constructing a list given a
function from indices to elements:

\begin{code}
tabulate : {n : Nat}{A : Set} -> (Fin n -> A) -> Vec A n
tabulate {zero}  f = []
tabulate {suc n} f = f fzero :: tabulate (f ∘ fsuc)
\end{code}

Note that \verb!tabulate! is defined by recursion over the length of the
result list, even though it is an implicit argument. There is in general no
correspondance between implicit data and computationally irrelevant data.

\subsection{Programs as proofs} \label{CurryHoward}

As mentioned in the introduction, Agda's type system is sufficiently
powerful to represent (almost) arbitrary propositions as types whose
elements are proofs of the proposition. Here are two very simple
propositions, the true proposition and the false proposition:

\begin{code}
data   False : Set where
record True  : Set where

trivial : True
trivial = _
\end{code}

The false proposition is represented by the datatype with no constructors
and the true proposition by the record type with no fields (see
Section \ref{Records} for more information on records). The record type
with no fields has a single element which is the empty record. We could have
defined \verb!True! as a datatype with a single element, but the nice thing
with the record definition is that the type checker knows that there is a
unique element of \verb!True! and will fill in any implicit arguments of
type \verb!True! with this element. This is exploited in the definition of
\verb!trivial! where the right hand side is just underscore. If you
nevertheless want to write the element of \verb!True!, the syntax is
\verb!record{}!.

These two propositions are enough to work with decidable propositions. We
can model decidable propositions as booleans and define

\begin{code}
isTrue : Bool -> Set
isTrue true  = True
isTrue false = False
\end{code}

Now, \verb!isTrue b! is the type of proofs that \verb!b! equals
\verb!true!. Using this technique we can define the safe list lookup
function in a different way, working on simply typed lists and numbers.

\begin{code}
_<_ : Nat -> Nat -> Bool
_     < zero  = false
zero  < suc n = true
suc m < suc n = m < n

length : {A : Set} -> List A -> Nat
length []        = zero
length (x :: xs) = suc (length xs)

lookup : {A : Set}(xs : List A)(n : Nat) ->
         isTrue (n < length xs) -> A
lookup []        n       ()
lookup (x :: xs) zero    p = x
lookup (x :: xs) (suc n) p = lookup xs n p
\end{code}

In this case, rather than there being no index into the empty list, there
is no proof that a number \verb!n! is smaller than \verb!zero!. In this
example using indexed types to capture the precondition is a little bit
nicer, since we don't have to pass around an explicit proof object, but
some properties cannot be easily captured by indexed types, in which case
this is a nice alternative.

We can also use datatype families to define propositions. Here is a
definition of the identity relation

\begin{code}
data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x
\end{code}

For a type \verb!A! and an element \verb!x! of \verb!A!, we define the the
family of proofs of ``being equal to \verb!x!''. This family is only
inhabited at index \verb!x! where the single proof is \verb!refl!.

Another example is the less than or equals relation on natural
numbers. This could be defined as a boolean function, as we have seen, but
we can also define it inductively

\begin{code}
data _≤_ : Nat -> Nat -> Set where
  leq-zero : {n : Nat} -> zero ≤ n
  leq-suc  : {m n : Nat} -> m ≤ n -> suc m ≤ suc n
\end{code}

One advantage of this approach is that we can pattern match on the proof
object. This makes proving properties of \verb!_≤_! easier. For instance,

\begin{code}
leq-trans : {l m n : Nat} -> l ≤ m -> m ≤ n -> l ≤ n
leq-trans leq-zero    _           = leq-zero
leq-trans (leq-suc p) (leq-suc q) = leq-suc (leq-trans p q)
\end{code}

\subsection{More on pattern matching}

We have seen how to pattern match on the arguments of a function, but
sometimes you want to pattern match on the result of some intermediate
computation. In Haskell and ML this is done on the right hand side using a
case or match expression. However, as we have learned, when pattern
matching on an expression in a dependently typed language, you not only
learn something about the shape of the expression, but you can also learn
things about other expressions. For instance, pattern matching on an
expression of type \verb!Vec A n! will reveal information about
\verb!n!. This is not captured by the usual case expression, so instead of
a case expression Agda provides a way of matching on intermediate
computations on the left hand side.

\subsubsection{The {\em with} construct}

The idea is that if you want to pattern match on an expression \verb!e! in
the definition of a function \verb!f!, you abstract \verb!f! over the value
of \verb!e!, effectively adding another argument to \verb!f! which can then
be matched on in the usual fashion. This abstraction is performed by the
\verb!with! construct. For instance,

\begin{code}
min : Nat -> Nat -> Nat
min x y with x < y
min x y | true  = x
min x y | false = y
\end{code}

The equations for \verb!min! following the with abstraction have an extra
argument, separated from the original arguments by a vertical bar,
corresponding to the value of the expression \verb!x < y!. You can abstract
over multiple expressions at the same time, separating them by vertical
bars and you can nest with abstractions. In the left hand side, with
abstracted arguments should be separated by vertical bars.

In this case pattern matching on \verb!x < y! doesn't tell us anything
interesting about the arguments of \verb!min!, so repeating the left hand
sides is a bit tedious. When this is the case you can replace the left hand
side with \verb!...!:

\begin{code}
filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x :: xs) with p x
... | true  = x :: filter p xs
... | false = filter p xs
\end{code}

Here is an example when we do learn something interesting. Given two
numbers we can compare them to see if they are equal. Rather than returning
an uninteresting boolean, we can return a proof that the numbers are indeed
equal when this is the case, and an explanation of why they are different
when this is the case:

\begin{code}
data _≠_ : Nat -> Nat -> Set where
  z≠s : {n : Nat} -> zero ≠ suc n
  s≠z : {n : Nat} -> suc n ≠ zero
  s≠s : {m n : Nat} -> m ≠ n -> suc m ≠ suc n

data Equal? (n m : Nat) : Set where
  eq  : n == m -> Equal? n m
  neq : n ≠ m -> Equal? n m
\end{code}

Two natural numbers are different if one is \verb!zero! and the other
\verb!suc! of something, or if both are successors but their predecessors
are different. Now we can define the function \verb!equal?! to check if two
numbers are equal:

\begin{code}
equal? : (n m : Nat) -> Equal? n m
equal? zero    zero    = eq refl
equal? zero    (suc m) = neq z≠s
equal? (suc n) zero    = neq s≠z
equal? (suc n) (suc m) with equal? n m
equal? (suc n) (suc .n) | eq refl = eq refl
equal? (suc n) (suc m)  | neq p   = neq (s≠s p)
\end{code}

Note that in the case where both numbers are successors we learn something
by pattern matching on the proof that the predecessors are equal. We will
see more examples of this kind of informative datatypes in
Section \ref{Views}.

When you abstract over an expression using \verb!with!, that expression is
abstracted from the entire context. This means that if the expression
occurs in the type of an argument to the function or in the result type,
this occurrence will be replaced by the with-argument on the left hand
side. For example, suppose we want to prove something about the
\verb!filter! function. That the only thing it does is throwing away some
elements of its argument, say. We can define what it means for one list to
be a sublist of another list:

\begin{code}
infix 20 _⊆_
data _⊆_ {A : Set} : List A -> List A -> Set where
  stop : [] ⊆ []
  drop : forall {xs y ys} -> xs ⊆ ys ->      xs ⊆ y :: ys
  keep : forall {x xs ys} -> xs ⊆ ys -> x :: xs ⊆ x :: ys
\end{code}

The intuition is that to obtain a sublist of a given list, each element can
either be dropped or kept. When the type checker can figure out the type of
an argument in a function type you can use the \verb!forall! syntax:
\begin{itemize}
  \item {\small \verb!forall {x y} a b -> A! } is short for
        {\small \verb!{x : _}{y : _}(a : _)(b : _) -> A!{}}.
\end{itemize}

Using this definition we can prove that
\verb!filter! computes a sublist of its argument:

\begin{code}
lem-filter : {A : Set}(p : A -> Bool)(xs : List A) ->
             filter p xs ⊆ xs
lem-filter p []        = stop
lem-filter p (x :: xs) with p x
... | true  = keep (lem-filter p xs) 
... | false = drop (lem-filter p xs) 
\end{code}

The interesting case is the \verb!_::_! case. Let us walk through it slowly:
\begin{code}
-- lem-filter p (x :: xs) = ?
\end{code}
At this point the goal that we have to prove is
\begin{code}
-- (filter p (x :: xs) | p x) ⊆ x :: xs
\end{code}
In the goal \verb!filter! has been applied to its with abstracted argument
\verb!p x! and will not reduce any further. Now, when we abstract over
\verb!p x! it will be abstracted from the goal type so we get
\begin{code}
-- lem-filter p (x :: xs) with p x
-- ... | px = ?
\end{code}
where \verb!p x! has been replaced by \verb!px! in the goal type
\begin{code}
-- (filter p (x :: xs) | px) ⊆ x :: xs
\end{code}
Now, when we pattern match on \verb!px! the call to \verb!filter! will
reduce and we get
\begin{code}
-- lem-filter p (x :: xs) with p x
-- ... | true  = ?  {- x :: filter p xs ⊆ x :: xs -}
-- ... | false = ?  {-      filter p xs ⊆ x :: xs -}
\end{code}

In some cases, it can be helpful to use \verb!with! to abstract over
an expression which you are not going to pattern match on. In particular,
if you expect this expression to be instantiated by pattern matching on
something else. Consider the proof that \verb!n + zero == n!:

\begin{code}
lem-plus-zero : (n : Nat) -> n + zero == n
lem-plus-zero zero = refl
lem-plus-zero (suc n) with n + zero | lem-plus-zero n
... | .n | refl = refl
\end{code}

In the step case we would like to pattern match on the induction hypothesis
\verb!n + zero == n! in order to prove \verb!suc n + zero == suc n!, but
since \verb!n + zero! cannot be unified with \verb!n! that is not
allowed. However, if we abstract over \verb!n + zero!, calling it \verb!m!,
we are left with the induction hypothesis \verb!m == n! and the goal
\verb!suc m == suc n!. Now we can pattern match on the induction
hypothesis, instantiating \verb!m! to \verb!n!.

\subsection{Modules} \label{Modules}

The module system in Agda is primarily used to manage name spaces. In a
dependently typed setting you could imagine having modules as first class
objects that could be passed around and created on the fly, but in Agda
this is not the case.

We have already seen that each file must define a single top-level module
containing all the declarations in the file. These declarations can in turn
be modules.

\begin{code}
module Maybe where
  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just    : A -> Maybe A

  maybe : {A B : Set} -> B -> (A -> B) -> Maybe A -> B
  maybe z f nothing  = z
  maybe z f (just x) = f x
\end{code}

By default all names declared in a module are visible from the outside. If
you want to hide parts of a module you can declare it \verb!private!:

\begin{code}
module A where
  private
    internal : Nat
    internal = zero

  exported : Nat -> Nat
  exported n = n + internal
\end{code}

To access public names from another module you can qualify the name by the
name of the module.
%
\begin{code}
mapMaybe₁ : {A B : Set} -> (A -> B) -> Maybe.Maybe A -> Maybe.Maybe B
mapMaybe₁ f Maybe.nothing  = Maybe.nothing
mapMaybe₁ f (Maybe.just x) = Maybe.just (f x)
\end{code}
%
Modules can also be opened, locally or on top-level:
%
\begin{code}
mapMaybe₂ : {A B : Set} -> (A -> B) -> Maybe.Maybe A -> Maybe.Maybe B
mapMaybe₂ f m = let open Maybe in maybe nothing (just ∘ f) m

open Maybe

mapMaybe₃ : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
mapMaybe₃ f m = maybe nothing (just ∘ f) m
\end{code}
%
When opening a module you can control which names are brought into scope
with the \verb!using!, \verb!hiding!, and \verb!renaming! keywords. For
instance, to open the \verb!Maybe! module without exposing the \verb!maybe!
function, and using different names for the type and the constructors we
can say
%
\begin{code}
open Maybe hiding (maybe)
           renaming (Maybe to _option; nothing to none; just to some)

mapOption : {A B : Set} -> (A -> B) -> A option -> B option
mapOption f none     = none
mapOption f (some x) = some (f x)
\end{code}
%
Renaming is just cosmetic, \verb!Maybe A! and \verb!A option! are
interchangable.
%
\begin{code}
mtrue : Maybe Bool
mtrue = mapOption not (just false)
\end{code}

\subsubsection{Parameterised modules}

Modules can be parameterised by arbitrary types\footnote{But not by other
modules.}.
%
\begin{code}
module Sort (A : Set)(_<_ : A -> A -> Bool) where
  insert : A -> List A -> List A
  insert y [] = y :: []
  insert y (x :: xs) with x < y
  ... | true  = x :: insert y xs
  ... | false = y :: x :: xs

  sort : List A -> List A
  sort []        = []
  sort (x :: xs) = insert x (sort xs)
\end{code}
%
When looking at the functions in parameterised module from the outside,
they take the module parameters as arguments, so
%
\begin{code}
sort₁ : (A : Set)(_<_ : A -> A -> Bool) -> List A -> List A
sort₁ = Sort.sort
\end{code}
%
You can apply the functions in a parameterised module to the module
parameters all at once, by instantiating the module
\begin{code}
module SortNat = Sort Nat _<_
\end{code}
%
This creates a new module \verb!SortNat! with functions \verb!insert! and
\verb!sort!.
%
\begin{code}
sort₂ : List Nat -> List Nat
sort₂ = SortNat.sort
\end{code}
Often you want to instantiate a module and open the result, in which case
you can simply write
\begin{code}
open Sort Nat _<_ renaming (insert to insertNat; sort to sortNat)
\end{code}
without having to give a name to the instantiated module.

Sometimes you want to export the contents of another module from the
current module. In this case you can open the module {\em publicly} using
the \verb!public! keyword:
\begin{code}
module Lists (A : Set)(_<_ : A -> A -> Bool) where
  open Sort A _<_ public
  minimum : List A -> Maybe A
  minimum xs with sort xs
  ... | []      = nothing
  ... | y :: ys = just y
\end{code}
Now the \verb!Lists! module will contain \verb!insert! and \verb!sort! as
well as the \verb!minimum! function.

\subsubsection{Importing modules from other files}

Agda programs can be split over multiple files. To use definitions from
a module defined in another file the module has to be {\em imported}.
Modules are imported by their names, so if you have a module \verb!A.B.C!
in a file \verb!/some/local/path/A/B/C.agda! it is imported with the
statement \verb!import A.B.C!. In order for the system to find the file
\verb!/some/local/path! must be in Agda's search path.\footnote{The search
path can be set from emacs by executing {\tt M-x customize-group agda2}.}.

I have a file \verb!Logic.agda! in the same directory as these notes,
defining logical conjunction and disjunction. To import it we say
\begin{code}
import Logic using (_∧_; _∨_)
\end{code}
Note that you can use the same namespace control keywords as when opening
modules. Importing a module does not automatically open it (like when you
say \verb!import qualified! in Haskell). You can either open it separately
with an open statement, or use the short form {\tt open import Logic}.

Splitting a program over several files will improve type checking
performance, since when you are making changes the type checker only has to
type check the files that are influenced by the changes.

\subsection{Records} \label{Records}

We have seen a record type already, namely the record type with no fields
which was used to model the true proposition. Now let us look at record
types with fields. A record type is declared much like a datatype where the
fields are indicated by the \verb!field! keyword. For instance
\begin{code}
record Point : Set where
  field x : Nat
        y : Nat
\end{code}
This declares a record type \verb!Point! with two natural number fields
\verb!x! and \verb!y!. To construct an element of \verb!Point! you write
\begin{code}
mkPoint : Nat -> Nat -> Point
mkPoint a b = record{ x = a; y = b }
\end{code}

To allow projection of the fields from a record, each record type comes
with a module of the same name. This module is parameterised by an element
of the record type and contains projection functions for the fields. In the
point example we get a module
\begin{code}
-- module Point (p : Point) where
--   x : Nat
--   y : Nat
\end{code}
This module can be used as it is or instantiated to a particular record.
\begin{code}
getX : Point -> Nat
getX = Point.x

abs² : Point -> Nat
abs² p = let open Point p in x * x + y * y
\end{code}

At the moment you cannot pattern match on records, but this will hopefully
be possible in a later version of Agda.

It is possible to add your own functions to the module of a record by
including them in the record declaration after the fields.

\begin{code}
record Monad (M : Set -> Set) : Set1 where
  field
    return : {A : Set} -> A -> M A
    _>>=_  : {A B : Set} -> M A -> (A -> M B) -> M B

  mapM : {A B : Set} -> (A -> M B) -> List A -> M (List B)
  mapM f [] = return []
  mapM f (x :: xs) = f x       >>= \y  ->
                     mapM f xs >>= \ys ->
                     return (y :: ys)

mapM' : {M : Set -> Set} -> Monad M ->
        {A B : Set} -> (A -> M B) -> List A -> M (List B)
mapM' Mon f xs = Monad.mapM Mon f xs
\end{code}
