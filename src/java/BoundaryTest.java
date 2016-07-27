import java.io.*;
import java.util.*;

public class BoundaryTest{

    public static final Vertex[] topPath = {VertexTest.a, VertexTest.b, VertexTest.c};
    public static final Vertex[] bottomPath = {VertexTest.a, VertexTest.c};
    public static final Boundary testBoundary = new Boundary(new ArrayList<Vertex>(Arrays.asList(topPath)),
							     new ArrayList<Vertex>(Arrays.asList(bottomPath)));

    public static void main(String[] args) throws FileNotFoundException {
	PrintWriter writer = new PrintWriter(args[0] + "/BoundaryTest.v");
	writer.println("Require Import List.");
	writer.println("Require Import Boundary.");
	writer.println();
	writer.println(testBoundary.toCoq().definition("testBoundary"));
	writer.close();
    }

}
