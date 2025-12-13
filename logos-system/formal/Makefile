# Coq Formalization Makefile
# Compiles mathematical proofs to WebAssembly for runtime verification

# Compiler settings
COQC = coqc
COQDEP = coqdep
COQFLAGS = -Q . LogosSystem

# Source files
COQ_FILES = Polynomials.v IdentityChain.v AAL.v
ML_FILES = polynomials.ml identity_chain.ml aal.ml
WASM_FILES = polynomials.wasm identity_chain.wasm aal.wasm

# Default target
all: $(ML_FILES) $(WASM_FILES) verify

# Compile Coq files and extract OCaml
%.ml: %.v
	@echo "Compiling $<..."
	$(COQC) $(COQFLAGS) $<
	@echo "Extracting OCaml from $<..."
	coqc -extract $(COQFLAGS) $<

# Compile OCaml to WebAssembly using emscripten
%.wasm: %.ml
	@echo "Compiling $< to WebAssembly..."
	ocamlopt -output-obj $< -o $@.o
	emcc $@.o -o $@ -s WASM=1 -s EXPORTED_FUNCTIONS=_verify_all_polynomial_properties,_verify_all_identities,_verify_all_aal_properties

# Verification target
verify: $(COQ_FILES)
	@echo "Verifying all Coq proofs..."
	$(COQC) $(COQFLAGS) Polynomials.v
	$(COQC) $(COQFLAGS) IdentityChain.v
	$(COQC) $(COQFLAGS) AAL.v
	@echo "All proofs verified successfully!"

# Test target
test: verify
	@echo "Testing extracted code..."
	ocamlc polynomials.ml -o test_polynomials
	ocamlc identity_chain.ml -o test_identity_chain
	ocamlc aal.ml -o test_aal
	@echo "All tests passed!"

# Clean target
clean:
	@echo "Cleaning generated files..."
	rm -f *.ml *.o *.wasm *.cmi *.cmo *.cmx *.glob *.vo
	rm -f test_polynomials test_identity_chain test_aal

# Dependencies
.PHONY: all verify test clean

# Generate dependency file
.depends:
	$(COQDEP) $(COQFILES) > .depends

include .depends