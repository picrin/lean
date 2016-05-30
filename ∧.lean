import data.prod
namespace hide
open prod

constant and : Prop → Prop → Prop

constant Proof : Prop → Type

constant and_intro : Π (p q : Prop), (Proof p) -> (Proof q) -> (Proof (and p q))

constant and_break : Π (p q : Prop), (Proof (and p q)) -> (Proof p) × (Proof q)

constants a b : Prop

constant anb : Proof (and a b)

definition first_step := and_break a b anb

definition second_step := and_intro b a (pr2 first_step) (pr1 first_step)

check second_step

end hide

