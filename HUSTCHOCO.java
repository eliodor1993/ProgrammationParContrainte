/*
 * This program help to generate the HUST master course time table 
 * by using the choco library
 * This file must be in the same package as the HUSTLS.java file 
 * in order to access to the classes defined inside it.
 */
package constrantprogramming;

import choco.Choco;
import choco.cp.model.CPModel;
import choco.cp.solver.CPSolver;
import choco.kernel.model.variables.integer.IntegerVariable;
import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Vector;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.jdom2.Document;
import org.jdom2.Element;
import org.jdom2.JDOMException;
import org.jdom2.input.SAXBuilder;

/**
 *
 * @author ELIODOR Ednalson Guy Mirlin, IFI 21th promotion, Hanoi 2017
 */
public class HUSTCHOCO {

    IntegerVariable[][] courseSlots;
    int[][] busySlotsTable;
    ArrayList<Courses> coursesList;
    ArrayList<Teachers> teachersList;
    int totalSlots;
    int nbCourses;
    int nbTeachers;
    Vector slotName;
    Vector className;
    CPModel m = new CPModel();

    //read data from xml file
    public void readData(String file) {

        SAXBuilder builder = new SAXBuilder();
        // Create the document
        Document doc;
        coursesList = new ArrayList<>();
        teachersList = new ArrayList<>();
        try {
            doc = builder.build(new File(file));
            Element racine = doc.getRootElement();
            List enfants = racine.getChildren();

            //read courses
            List course = ((Element) enfants.get(0)).getChildren();
            nbCourses = course.size();
            for (int j = 0; j < course.size(); j++) {
                Element node = (Element) course.get(j);

                int id = Integer.parseInt(node.getChildText("id"));
                int teacherId = Integer.parseInt(node.getChildText("teacher"));
                Vector courseClasses = new Vector();
                String courseName = node.getChildText("name");
                List classes = node.getChildren("class");

                for (int k = 0; k < classes.size(); k++) {

                    courseClasses.addElement(Integer.parseInt(((Element) classes.get(k)).getText()));
                }
//                for (int k = 0; k < classes.size(); k++) {
//                    System.out.println((int) (courseClasses.get(k)));
//                }
                int classeId = Integer.parseInt(node.getChildText("class"));
                int nbSlots = Integer.parseInt(node.getChildText("nbSlots"));
                coursesList.add(new Courses(id, teacherId, courseClasses, nbSlots, courseName));
            }

            //read slots
            List slots = ((Element) enfants.get(1)).getChildren();
            totalSlots = slots.size();
            slotName = new Vector();
            for (int j = 0; j < slots.size(); j++) {
                Element node = (Element) slots.get(j);
                slotName.addElement(node.getChildText("name"));
            }
            
            //read teachers
            List teacher = ((Element) enfants.get(2)).getChildren();
            nbTeachers = teacher.size();
            for (int j = 0; j < teacher.size(); j++) {
                Element node = (Element) teacher.get(j);

                int id = Integer.parseInt(node.getChildText("id"));
                String teacherName = node.getChildText("name");
                Vector busySlotsList = new Vector();
                List teacherBusySlots = node.getChildren("busy");
                for (int k = 0; k < teacherBusySlots.size(); k++) {
                    busySlotsList.addElement(Integer.parseInt(((Element) teacherBusySlots.get(k)).getChildText("slot")));
                }

                teachersList.add(new Teachers(id, busySlotsList,teacherName));
            }
            
            //read classes
            List classes = ((Element) enfants.get(3)).getChildren(); 
            className = new Vector();
            for (int j = 0; j < classes.size(); j++) {
                Element node = (Element) classes.get(j);
                className.addElement(node.getChildText("name"));
            }

        } catch (JDOMException ex) {
            Logger.getLogger(testxml.class.getName()).log(Level.SEVERE, null, ex);
        } catch (IOException ex) {
            Logger.getLogger(testxml.class.getName()).log(Level.SEVERE, null, ex);
        }

    }

    public void stateModel() {

        courseSlots = new IntegerVariable[nbCourses][];
        for (int i = 0; i < nbCourses; i++) {
            courseSlots[i] = new IntegerVariable[coursesList.get(i).nbSlots];
            for (int j = 0; j < coursesList.get(i).nbSlots; j++) {
                courseSlots[i][j] = Choco.makeIntVar("courseSlots" + i + j, 1, totalSlots);
            }
        }

        //constraint on teacher busy slots
        IntegerVariable[] x;
        int currentCourseSlots;
        Vector currentTeacherBusySlots;
        for (int i = 0; i < nbCourses; i++) {
            currentCourseSlots = coursesList.get(i).nbSlots;
            currentTeacherBusySlots = teachersList.get((coursesList.get(i).teacherId) - 1).busySlots;
            x = new IntegerVariable[currentCourseSlots + currentTeacherBusySlots.size()];

            for (int j = 0; j < x.length; j++) {
                if (j < currentCourseSlots) {
                    x[j] = courseSlots[i][j];
                } else {
                    x[j] = new IntegerVariable("x" + j, (int) currentTeacherBusySlots.get(j - currentCourseSlots), (int) currentTeacherBusySlots.get(j - currentCourseSlots));
                }

            }
            m.addConstraint(Choco.allDifferent(x));
        }

        //constraint on courses assigned to a same classe
        IntegerVariable[] y;
        for (int i = 0; i < coursesList.size() - 1; i++) {
            for (int j = i + 1; j < coursesList.size(); j++) {
                for (int l = 0; l < coursesList.get(j).classeId.size(); l++) {
                    if (coursesList.get(i).classeId.contains(coursesList.get(j).classeId.get(l))) {
                        y = new IntegerVariable[coursesList.get(i).nbSlots + coursesList.get(j).nbSlots];
                        for (int k = 0; k < y.length; k++) {
                            if (k < coursesList.get(i).nbSlots) {
                                y[k] = courseSlots[i][k];
                            } else {
                                y[k] = courseSlots[j][k - coursesList.get(i).nbSlots];
                            }
                        }
                        m.addConstraint(Choco.allDifferent(y));
                    }
                }
            }
        }

        //constraint on courses assigned to a same teacher
        IntegerVariable[] z;
        for (int i = 0; i < coursesList.size() - 1; i++) {
            for (int j = i + 1; j < coursesList.size(); j++) {

                if (coursesList.get(i).teacherId == coursesList.get(j).teacherId) {
                    z = new IntegerVariable[coursesList.get(i).nbSlots + coursesList.get(j).nbSlots];
                    for (int k = 0; k < z.length; k++) {
                        if (k < coursesList.get(i).nbSlots) {
                            z[k] = courseSlots[i][k];
                        } else {
                            z[k] = courseSlots[j][k - coursesList.get(i).nbSlots];
                        }
                    }
                    m.addConstraint(Choco.allDifferent(z));
                }
            }
        }
    }

          public void writeHTML(String fn, CPSolver s){
		try{     
                    
			PrintWriter out = new PrintWriter(fn); 
                        
                        out.println("<head>");
                        out.println("<meta http-equiv=\"Content-Type\" content=\"text/html; charset=utf-8\">");
                        out.println("</head>");
                        out.println("<body>");                       
                        out.println("<table border = 1>");  
                         out.println("<caption> HUST MASTER COURSES TIME TABLE GENERATED BY CHOCO </caption>");
                        out.println("<tr bgcolor='lightblue'>");
                            out.println("<th width = 40> Num Cours </th>");
                            out.println("<th width = 300> Nom Cours </th>");
                            out.println("<th> Num et nom classes </th>");
                            out.println("<th width = 40 > Nbre fragements </th>");
                            out.println("<th> Num et nom profs </th>");
                            out.println("<th> Slots assignés </th>");
                        out.println("</tr>");
			for(int i = 0; i < nbCourses; i++){
				out.println("<tr bgcolor='lightgray'>");
				
					out.println("<td>");
					out.println((i+1));
					out.println("</td>");
                                        out.println("<td>");
					out.println(coursesList.get(i).courseName);
					out.println("</td>"); 
                                         out.println("<td>");
                                        for(int j = 0; j < coursesList.get(i).classeId.size(); j++){
					out.println(coursesList.get(i).classeId.get(j)+"  "+ className.get((int)coursesList.get(i).classeId.get(j)-1)+"<br/> ");
                                        }
					out.println("</td>");
                                        out.println("<td>");
					out.println(coursesList.get(i).nbSlots);
					out.println("</td>");                                       
                                        out.println("<td>");
					out.println(coursesList.get(i).teacherId+ "  " +teachersList.get(coursesList.get(i).teacherId-1).teacherName );
					out.println("</td>");
                                        out.println("<td>");
                                        for(int k = 0; k < coursesList.get(i).nbSlots; k++){
					out.println(s.getVar(courseSlots[i][k]).getVal() + " "+slotName.get(s.getVar(courseSlots[i][k]).getVal()-1)+ "<br/> ");
                                        }
					out.println("</td>"); 
				
				out.println("</tr>");
			}
			out.println("</table>");                     
                        out.println("</body>");
			out.close();
		}catch(Exception e){
			e.printStackTrace();
		}
	}

    
    
    
    public void afficherResultat(CPSolver s) {

        for (int i = 0; i < nbCourses; i++) {
            System.out.print("cours " + (i + 1) + ":  ");
            for (int j = 0; j < coursesList.get(i).nbSlots; j++) {
                System.out.print(s.getVar(courseSlots[i][j]).getVal() + " ");
            }
            System.out.println();
        }
    }

    public void search() {
        CPSolver s = new CPSolver();
        s.read(m);
        s.solve();
        afficherResultat(s);
        writeHTML("HUSTCHOCO.html", s);
        

    }

    public static void main(String[] args) {
        HUSTCHOCO hustlsChoco = new HUSTCHOCO();
        hustlsChoco.readData("data.xml");
        hustlsChoco.stateModel();
        hustlsChoco.search();
    }
}
