#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char *argv[])
{
    FILE *f;
    FILE *g;
    unsigned data;
    int addr = 0;
    f = fopen(argv[1], "r");
    if (!f)
        return -1;
    g = fopen(argv[2], "w");
    if (!g)
        return -1;
    if (!strcmp(argv[3], "word"))
    {
        while (1 == fread(&data, 4, 1, f)) {
            // Verilog case statement
            // printf("    16'h%4.4x: rd_data <= 32'h%8.8x;\n", addr, data);
            // For readmemh
            fprintf(g, "%8.8x\n", data);
            addr++;
        }
    }
    else if(!strcmp(argv[3], "byte0"))
    {
        while (1 == fread(&data, 4, 1, f)) {
            // Verilog case statement
            // printf("    16'h%4.4x: rd_data <= 32'h%8.8x;\n", addr, data);
            // For readmemh
            fprintf(g, "%2.2x\n", 255 & (data >> 0));
            addr++;
        }
    }
    else if(!strcmp(argv[3], "byte1"))
    {
        while (1 == fread(&data, 4, 1, f)) {
            // Verilog case statement
            // printf("    16'h%4.4x: rd_data <= 32'h%8.8x;\n", addr, data);
            // For readmemh
            fprintf(g, "%2.2x\n", 255 & (data >> 8));
            addr++;
        }
    }
    else if(!strcmp(argv[3], "byte2"))
    {
        while (1 == fread(&data, 4, 1, f)) {
            // Verilog case statement
            // printf("    16'h%4.4x: rd_data <= 32'h%8.8x;\n", addr, data);
            // For readmemh
            fprintf(g, "%2.2x\n", 255 & (data >> 16));
            addr++;
        }
    }
    else if(!strcmp(argv[3], "byte3"))
    {
        while (1 == fread(&data, 4, 1, f)) {
            // Verilog case statement
            // printf("    16'h%4.4x: rd_data <= 32'h%8.8x;\n", addr, data);
            // For readmemh
            fprintf(g, "%2.2x\n", 255 & (data >> 24));
            addr++;
        }
    }
    fclose(g);
    fclose(f);
    return 0;
}
