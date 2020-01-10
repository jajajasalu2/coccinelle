@ r0 @
type t;
position p;
@@
t@p

@ script:python r1 @
id;
@@
coccinelle.id = "id/* user comment */"

@ r2 @
identifier r1.id;
type r0.t;
@@
foo() {
...
++ t id;
}
