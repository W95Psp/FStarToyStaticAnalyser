cd out
# echo "let main = print_string \"Number? \"; let strline = read_line () in print_string (Main.getStr strline (Prims.parse_int \"2\"))" > Exec.ml
# echo "let main = print_string \"Number? \"; let strline = read_line () in print_string (Main.getStr strline (Prims.parse_int strline))" > Exec.ml
OCAMLPATH=/home/FStar/FStar/bin ocamlbuild -package fstarlib,fstar-tactics-lib,fstar-compiler-lib "Main.native"
# OCAMLPATH=/home/FStar/FStar/bin ocamlbuild -package fstarlib,fstar-tactics-lib,fstar-compiler-lib "Exec.native"
echo ""
echo ""
./Main.native
# ./Exec.native
echo ""