namespace hidden
inductive empty : Type

inductive unit : Type
| star : unit

inductive bool : Type
| ff : bool
| tt : bool

#check ff
#check bool.ff
#check hidden.bool.ff

#print ff
#print bool.ff
#print hidden.bool.ff

#check bool
#check hidden.bool

def band (b1 b2 : bool) : bool :=
bool.cases_on b1 bool.ff b2

#reduce band bool.ff bool.ff
#reduce band bool.ff bool.tt
#reduce band bool.tt bool.ff
#reduce band bool.tt bool.tt

def bor (b1 b2 : bool) : bool :=
bool.cases_on b1 b2 bool.tt

#reduce bor bool.ff bool.ff
#reduce bor bool.ff bool.tt
#reduce bor bool.tt bool.ff
#reduce bor bool.tt bool.tt

def bnot (b : bool) : bool :=
bool.cases_on b bool.tt bool.ff

#reduce bnot bool.ff
#reduce bnot bool.tt

end hidden
