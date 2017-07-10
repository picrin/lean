inductive natural : Type
| zero : natural
| succ : natural → natural


#check natural.succ natural.zero

definition isZero : natural -> Prop :=
  assume (d : natural), natural.rec_on d true (λ (x1: natural) (x2 : Prop), false)

#eval isZero natural.zero

#eval isZero (natural.succ natural.zero)

#check @nat.rec_on

def addition (m n : natural) : natural :=
  natural.rec_on n m (λ (n : natural) (add_m_n : natural), natural.succ add_m_n)








inductive natural : Type
| zero : natural
| succ : natural → natural


#check natural.succ natural.zero

definition isZero : natural -> Prop :=
  assume (d : natural), natural.rec_on d true (λ (x1: natural) (x2 : Prop), false)

#eval isZero natural.zero

#eval isZero (natural.succ natural.zero)

#check @nat.rec_on

def addition (m n : natural) : natural :=
  natural.rec_on n 
    -- case n = 0
    m 
    -- case n = succ n'
    (λ (n' : natural) (n'_add_m : natural), natural.succ n'_add_m)
    
set_option pp.all true
#print addition

def Add : nat → nat → nat
| 0 m := m
| (nat.succ n) m := nat.succ (Add n m)

#reduce 10 * 20000

