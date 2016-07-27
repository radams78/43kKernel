import java.io.*;
import java.util.*;

public class BoundaryTest{

    public static void main(String[] args) throws FileNotFoundException {
	PrintWriter writer = new PrintWriter(args[0] + "/BoundaryTest.v");
	writer.println("Require Import List.");
	writer.println("Require Import Boundary.");
	writer.println();
	Vertex a = new Vertex(0);
	Vertex b = new Vertex(1);
	Vertex c = new Vertex(2);
	Vertex[] topPath = {a, b, c};
	Vertex[] bottomPath = {a, c};
	Boundary testBoundary = new Boundary(new ArrayList<Vertex>(Arrays.asList(topPath)), 
					     new ArrayList<Vertex>(Arrays.asList(bottomPath)));
	writer.println(testBoundary.toCoq().definition("testBoundary"));
	writer.close();
    }

}
