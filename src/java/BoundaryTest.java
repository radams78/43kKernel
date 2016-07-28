import java.io.*;
import java.util.*;

public class BoundaryTest{

    public static final Vertex[] topPath = {VertexTest.a, VertexTest.b, VertexTest.c};
    public static final Vertex[] bottomPath = {VertexTest.a, VertexTest.c};
    public static final Boundary testBoundary = new Boundary(new Path(Arrays.asList(topPath)),
							     new Path(Arrays.asList(bottomPath)));

    public static void main(String[] args) throws FileNotFoundException {
	PrintWriter writer = new PrintWriter(args[0] + "/BoundaryTest.v");
	writer.println("Require Import List.");
	writer.println("Require Import Boundary."); // TODO Duplication
	writer.println();
	writer.println(testBoundary.definition("testBoundary"));
	writer.close();
    }

}
