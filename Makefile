all: bin doc src/coq/BoundaryTest.vo src/coq/BasicRegionTest.vo src/coq/BasicRegionGeneratorTest.vo
bin: $(shell ls src/java/*.java)
	javac -d bin src/java/*.java
doc:
	javadoc -d doc src/java/*.java
src/coq/%.vo: bin
	@cd bin; java $* ../src/coq
	@cd src/coq; coqc $*
