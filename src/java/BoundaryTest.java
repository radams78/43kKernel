import java.io.*;
import java.util.*;

//TODO Add tests that should fail

public class BoundaryTest{

    public static final Vertex[] topPath = {VertexTest.a, VertexTest.b, VertexTest.c, VertexTest.d};
    public static final Vertex[] bottomPath = {VertexTest.a, VertexTest.d};
    public static final Boundary testBoundary = new Boundary(new Path(Arrays.asList(topPath)),
							     new Path(Arrays.asList(bottomPath)));
    public static final String[] IMPORTS = { "Vector", "Boundary" };
    public static final String FILENAME = "BoundaryTest.v";
    public static final String NAME = "testBoundary";

    //TODO Duplication with CoqObjectTest
    public static void main(String[] args) throws FileNotFoundException {
	PrintWriter writer = new PrintWriter(args[0] + "/" + FILENAME);
	for (String imp : IMPORTS)
	    writer.println(CoqObjectTest.REQUIRE_IMPORT + " " + imp + ".");
	writer.println("Import VectorNotations.");
	writer.println();
	writer.println(testBoundary.definition(NAME));
	writer.close();
    }

}
