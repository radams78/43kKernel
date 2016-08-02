import java.io.*;
import java.util.*;

public class BoundaryTest{

    public static final Vertex[] topPath = {VertexTest.a, VertexTest.b, VertexTest.c};
    public static final Vertex[] bottomPath = {VertexTest.a, VertexTest.c};
    public static final Boundary testBoundary = new Boundary(new Path(Arrays.asList(topPath)),
							     new Path(Arrays.asList(bottomPath)));
    public static final String[] IMPORTS = { "Vector", "Boundary" };
    public static final String FILENAME = "BoundaryTest.v";
    public static final String NAME = "testBoundary";

    public static void main(String[] args) throws FileNotFoundException {
	CoqObjectTest.testObject(args[0], FILENAME, IMPORTS, testBoundary, NAME);
    }

}
