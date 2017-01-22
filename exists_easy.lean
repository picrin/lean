section
    variable U : Type
    variable P : U → Prop
    variable p : Prop
    

    variable Hforall : (∀ v : U, P v → p)
    
    variable Hexist : (∃ u : U, P u)
    
    theorem t1 : p :=
        have H : (Π a, P a → p) → p, from exists.elim Hexist,
        H Hforall
    
    check exists.elim Hexist
    
end
