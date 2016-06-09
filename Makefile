all: bin doc src/coq/BoundaryTest.vo
bin:
	javac -d bin src/java/*.java
doc:
	javadoc -d doc src/java/*.java
src/coq/BoundaryTest.vo:
	@cd bin; java BoundaryTest ../src/coq
	@cd src/coq; coqc BoundaryTest
