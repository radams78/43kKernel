import java.io.*;
import java.util.*;

public class BoundaryTest{

    public static void main(String[] args) throws FileNotFoundException {
	PrintWriter writer = new PrintWriter(args[0] + "/BoundaryTest.v");
	writer.println("Require Import List.");
	writer.println("Require Import Boundary.");
	writer.println();
	Integer[] topPath = {0, 1, 2};
	Integer[] bottomPath = {0, 2};
	Boundary testBoundary = new Boundary(new ArrayList<Integer>(Arrays.asList(topPath)), 
					     new ArrayList<Integer>(Arrays.asList(bottomPath)),
					     "testBoundary");
	writer.println(testBoundary.toCoq().definition("testBoundary"));
	writer.close();
    }

}
