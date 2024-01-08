declare let window: Window & {
    hakimQuery: (x: any) => any;
};
export const hakimQueryImpl = async (json_obj: any): Promise<any> => {
    return window.hakimQuery(json_obj);;
};