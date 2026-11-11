export interface Invoice {
  id: string;
  total: number;
}

// The one function the ReScript file imports.
export function invoiceTotal(invoice: Invoice): number {
  return invoice.total;
}

// The rest of the module is never type checked for the import. That is why
// the mistake below goes unnoticed, and why the import is fast.
export function broken(): number {
  return missingVariable * 2;
}

export function report1(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:1` }));
  return table.filter((entry) => entry.row.total > 1).map((entry) => entry.label.length + entry.index);
}

export function report2(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:2` }));
  return table.filter((entry) => entry.row.total > 2).map((entry) => entry.label.length + entry.index);
}

export function report3(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:3` }));
  return table.filter((entry) => entry.row.total > 3).map((entry) => entry.label.length + entry.index);
}

export function report4(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:4` }));
  return table.filter((entry) => entry.row.total > 4).map((entry) => entry.label.length + entry.index);
}

export function report5(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:5` }));
  return table.filter((entry) => entry.row.total > 5).map((entry) => entry.label.length + entry.index);
}

export function report6(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:6` }));
  return table.filter((entry) => entry.row.total > 6).map((entry) => entry.label.length + entry.index);
}

export function report7(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:7` }));
  return table.filter((entry) => entry.row.total > 7).map((entry) => entry.label.length + entry.index);
}

export function report8(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:8` }));
  return table.filter((entry) => entry.row.total > 8).map((entry) => entry.label.length + entry.index);
}

export function report9(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:9` }));
  return table.filter((entry) => entry.row.total > 9).map((entry) => entry.label.length + entry.index);
}

export function report10(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:10` }));
  return table.filter((entry) => entry.row.total > 10).map((entry) => entry.label.length + entry.index);
}

export function report11(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:11` }));
  return table.filter((entry) => entry.row.total > 11).map((entry) => entry.label.length + entry.index);
}

export function report12(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:12` }));
  return table.filter((entry) => entry.row.total > 12).map((entry) => entry.label.length + entry.index);
}

export function report13(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:13` }));
  return table.filter((entry) => entry.row.total > 13).map((entry) => entry.label.length + entry.index);
}

export function report14(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:14` }));
  return table.filter((entry) => entry.row.total > 14).map((entry) => entry.label.length + entry.index);
}

export function report15(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:15` }));
  return table.filter((entry) => entry.row.total > 15).map((entry) => entry.label.length + entry.index);
}

export function report16(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:16` }));
  return table.filter((entry) => entry.row.total > 16).map((entry) => entry.label.length + entry.index);
}

export function report17(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:17` }));
  return table.filter((entry) => entry.row.total > 17).map((entry) => entry.label.length + entry.index);
}

export function report18(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:18` }));
  return table.filter((entry) => entry.row.total > 18).map((entry) => entry.label.length + entry.index);
}

export function report19(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:19` }));
  return table.filter((entry) => entry.row.total > 19).map((entry) => entry.label.length + entry.index);
}

export function report20(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:20` }));
  return table.filter((entry) => entry.row.total > 20).map((entry) => entry.label.length + entry.index);
}

export function report21(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:21` }));
  return table.filter((entry) => entry.row.total > 21).map((entry) => entry.label.length + entry.index);
}

export function report22(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:22` }));
  return table.filter((entry) => entry.row.total > 22).map((entry) => entry.label.length + entry.index);
}

export function report23(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:23` }));
  return table.filter((entry) => entry.row.total > 23).map((entry) => entry.label.length + entry.index);
}

export function report24(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:24` }));
  return table.filter((entry) => entry.row.total > 24).map((entry) => entry.label.length + entry.index);
}

export function report25(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:25` }));
  return table.filter((entry) => entry.row.total > 25).map((entry) => entry.label.length + entry.index);
}

export function report26(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:26` }));
  return table.filter((entry) => entry.row.total > 26).map((entry) => entry.label.length + entry.index);
}

export function report27(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:27` }));
  return table.filter((entry) => entry.row.total > 27).map((entry) => entry.label.length + entry.index);
}

export function report28(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:28` }));
  return table.filter((entry) => entry.row.total > 28).map((entry) => entry.label.length + entry.index);
}

export function report29(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:29` }));
  return table.filter((entry) => entry.row.total > 29).map((entry) => entry.label.length + entry.index);
}

export function report30(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:30` }));
  return table.filter((entry) => entry.row.total > 30).map((entry) => entry.label.length + entry.index);
}

export function report31(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:31` }));
  return table.filter((entry) => entry.row.total > 31).map((entry) => entry.label.length + entry.index);
}

export function report32(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:32` }));
  return table.filter((entry) => entry.row.total > 32).map((entry) => entry.label.length + entry.index);
}

export function report33(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:33` }));
  return table.filter((entry) => entry.row.total > 33).map((entry) => entry.label.length + entry.index);
}

export function report34(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:34` }));
  return table.filter((entry) => entry.row.total > 34).map((entry) => entry.label.length + entry.index);
}

export function report35(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:35` }));
  return table.filter((entry) => entry.row.total > 35).map((entry) => entry.label.length + entry.index);
}

export function report36(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:36` }));
  return table.filter((entry) => entry.row.total > 36).map((entry) => entry.label.length + entry.index);
}

export function report37(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:37` }));
  return table.filter((entry) => entry.row.total > 37).map((entry) => entry.label.length + entry.index);
}

export function report38(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:38` }));
  return table.filter((entry) => entry.row.total > 38).map((entry) => entry.label.length + entry.index);
}

export function report39(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:39` }));
  return table.filter((entry) => entry.row.total > 39).map((entry) => entry.label.length + entry.index);
}

export function report40(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:40` }));
  return table.filter((entry) => entry.row.total > 40).map((entry) => entry.label.length + entry.index);
}

export function report41(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:41` }));
  return table.filter((entry) => entry.row.total > 41).map((entry) => entry.label.length + entry.index);
}

export function report42(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:42` }));
  return table.filter((entry) => entry.row.total > 42).map((entry) => entry.label.length + entry.index);
}

export function report43(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:43` }));
  return table.filter((entry) => entry.row.total > 43).map((entry) => entry.label.length + entry.index);
}

export function report44(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:44` }));
  return table.filter((entry) => entry.row.total > 44).map((entry) => entry.label.length + entry.index);
}

export function report45(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:45` }));
  return table.filter((entry) => entry.row.total > 45).map((entry) => entry.label.length + entry.index);
}

export function report46(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:46` }));
  return table.filter((entry) => entry.row.total > 46).map((entry) => entry.label.length + entry.index);
}

export function report47(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:47` }));
  return table.filter((entry) => entry.row.total > 47).map((entry) => entry.label.length + entry.index);
}

export function report48(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:48` }));
  return table.filter((entry) => entry.row.total > 48).map((entry) => entry.label.length + entry.index);
}

export function report49(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:49` }));
  return table.filter((entry) => entry.row.total > 49).map((entry) => entry.label.length + entry.index);
}

export function report50(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:50` }));
  return table.filter((entry) => entry.row.total > 50).map((entry) => entry.label.length + entry.index);
}

export function report51(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:51` }));
  return table.filter((entry) => entry.row.total > 51).map((entry) => entry.label.length + entry.index);
}

export function report52(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:52` }));
  return table.filter((entry) => entry.row.total > 52).map((entry) => entry.label.length + entry.index);
}

export function report53(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:53` }));
  return table.filter((entry) => entry.row.total > 53).map((entry) => entry.label.length + entry.index);
}

export function report54(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:54` }));
  return table.filter((entry) => entry.row.total > 54).map((entry) => entry.label.length + entry.index);
}

export function report55(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:55` }));
  return table.filter((entry) => entry.row.total > 55).map((entry) => entry.label.length + entry.index);
}

export function report56(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:56` }));
  return table.filter((entry) => entry.row.total > 56).map((entry) => entry.label.length + entry.index);
}

export function report57(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:57` }));
  return table.filter((entry) => entry.row.total > 57).map((entry) => entry.label.length + entry.index);
}

export function report58(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:58` }));
  return table.filter((entry) => entry.row.total > 58).map((entry) => entry.label.length + entry.index);
}

export function report59(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:59` }));
  return table.filter((entry) => entry.row.total > 59).map((entry) => entry.label.length + entry.index);
}

export function report60(rows: Invoice[]) {
  const table = rows.map((row, index) => ({ row, index, label: `${row.id}:60` }));
  return table.filter((entry) => entry.row.total > 60).map((entry) => entry.label.length + entry.index);
}
